/**
 * Do not submit your assignment with a main function in this file.
 * If you submit with a main function in this file, you will get a zero.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include "debug.h"
#include "sfmm.h"

static int firstMallocFlag = 1;
static int noMemoryRemaining = 0;
static double totalPayloadSize = 0;
static double maxAggregatePayload = 0;
static double totalBlockSize = 0;

static void initializeFreeLists();
static void formatFirstPage();
static void extendHeap();
static int determineFreeListIndex(size_t blockSize);
static void writeBlock(sf_block *inputBlock, int payloadSize, int blockSize, int alloc, int prevAlloc);
static void encodeEpilogue(int prevAlloc);
static size_t findPayload(size_t header);
static size_t findBlockSize(size_t header);
static int isAllocated(size_t header);
static int isPrevAllocated(size_t prevFooter);
static void determineSplit(sf_block *suitableBlock, size_t reqBlockSize, size_t payloadSize, int isWilderness, int reallocMod);
static void removeFromFreeList(sf_block *inputBlock);
static void addToFreeList(sf_block *inputBlock, int listIndex);
static void verifyPointer(void *ptr);
static void totalPayloadCalculation(size_t payload);

void *sf_malloc(size_t size) {
    if (firstMallocFlag) {
        initializeFreeLists();
        formatFirstPage();
        firstMallocFlag = 0;
    }

    // Input validation
    if (size == 0) return NULL;

    // Variable declarations
    int suitableBlockFound = 0;
    int listIndex = 0;
    int isWilderness= 0;
    size_t reqBlockSize = 0;
    size_t currentBlockSize = 0;
    sf_block *headBlock = NULL;
    sf_block *currentBlock = NULL;
    sf_block *suitableBlock = NULL;

    // Calculates required block size, including header and footer
    reqBlockSize = ((size + 31) / 16) * 16;

    // Determines minimum free list sufficient to hold block
    listIndex = determineFreeListIndex(reqBlockSize);

    DETERMINE_FREE_LIST:

    // Check current FREE_LIST for suitable block
    for (int i = listIndex; i < NUM_FREE_LISTS; i++) { // Iterates through free list to wilderness
        headBlock = &sf_free_list_heads[i];
        currentBlock = headBlock->body.links.next;
        while (currentBlock != headBlock) { // Iterates through circular linked list
            currentBlockSize = findBlockSize(currentBlock->header);
            if ((int)currentBlockSize >= reqBlockSize) {
                if (i == (NUM_FREE_LISTS - 1)) isWilderness = 1;
                suitableBlock = currentBlock;
                suitableBlockFound = 1;
                goto SUITABLE_BLOCK_FOUND;
            }
            currentBlock = currentBlock->body.links.next;
        }
    }

    SUITABLE_BLOCK_FOUND:

    if (!suitableBlockFound) { // No suitable block found, must extend heap
        extendHeap();
        if (noMemoryRemaining) {
            sf_errno = ENOMEM;
            return NULL;
        }
        suitableBlock = sf_free_list_heads[NUM_FREE_LISTS - 1].body.links.next;
        goto DETERMINE_FREE_LIST;
        isWilderness = 1;

    }

    // Allocates block, splits if possible
    determineSplit(suitableBlock, reqBlockSize, size, isWilderness, 0);

    // Check to rewrite epilogue if necessary
    currentBlock = sf_free_list_heads[NUM_FREE_LISTS - 1].body.links.next;
    if (currentBlock == &sf_free_list_heads[NUM_FREE_LISTS - 1]) encodeEpilogue(1);

    // Sets pointer for output
    void *output = (void*)suitableBlock;
    output = (char*)output;
    output += 16;
    return (void*)output;

    abort();
}

// Runs when malloc is first called, initializes free lists, sets head pointers to themselves
static void initializeFreeLists() {
    for (int i = 0; i < NUM_FREE_LISTS; i++) {
        sf_free_list_heads[i].body.links.next = &sf_free_list_heads[i];
        sf_free_list_heads[i].body.links.prev = &sf_free_list_heads[i];
    }
}

// Runs when malloc is first called, initializes heap, encodes prologue and epilogue, creates wilderness block
static void formatFirstPage() {
    sf_mem_grow();

    // Encode prologue
    sf_block *prologue = (sf_block*)sf_mem_start();
    writeBlock(prologue, 0, 32, 1, 0);

    // Create wilderness block
    void *ptr = sf_mem_start();
    ptr = (char*)ptr;
    ptr += 32;
    sf_block *wilderness = (sf_block*)ptr;
    writeBlock(wilderness, 0, 4048, 0, 1);

    // Encode epilogue
    encodeEpilogue(0);

    // Add wilderness block to free list[NUM_FREE_LISTS - 1]
    wilderness->body.links.next = &sf_free_list_heads[NUM_FREE_LISTS - 1];
    wilderness->body.links.prev = &sf_free_list_heads[NUM_FREE_LISTS - 1];
    sf_free_list_heads[NUM_FREE_LISTS - 1].body.links.next = wilderness;
    sf_free_list_heads[NUM_FREE_LISTS - 1].body.links.prev = wilderness;
}

// Extends heap by coalescing free space with wilderness block
static void extendHeap() {
    // Calculate prevAlloc and set tempPtr if wilderness block does not exist
    void *endPtr = sf_mem_end();
    endPtr = (char*)endPtr;
    endPtr -= 16;
    sf_block *tempBlock = endPtr;
    int prevAlloc = isPrevAllocated(tempBlock->header);
    void *tempPtr = endPtr;

    size_t blockSize = 0;

    // Checks if wilderness block exists
    sf_block *wildernessBlock = sf_free_list_heads[NUM_FREE_LISTS - 1].body.links.next;
    if (wildernessBlock != &sf_free_list_heads[NUM_FREE_LISTS - 1]) {
        tempPtr = wildernessBlock;
    }

    void *memoryRemaining = sf_mem_grow();
    if (memoryRemaining == NULL) {
        noMemoryRemaining = 1;
        return;
    }

    // Calculates wilderness block size and encodes it
    endPtr = sf_mem_end();
    endPtr = (char*)endPtr;
    endPtr -= 16;
    blockSize = endPtr - tempPtr;
    writeBlock(tempPtr, 0, blockSize, 0, prevAlloc);

    // Add wilderness block to free list
    wildernessBlock = tempPtr;
    wildernessBlock->body.links.next = &sf_free_list_heads[NUM_FREE_LISTS - 1];
    wildernessBlock->body.links.prev = &sf_free_list_heads[NUM_FREE_LISTS - 1];
    sf_free_list_heads[NUM_FREE_LISTS - 1].body.links.next = wildernessBlock;
    sf_free_list_heads[NUM_FREE_LISTS - 1].body.links.prev = wildernessBlock;
}

// Determines which free list a block belongs to based on block size
static int determineFreeListIndex(size_t blockSize) {
    double blockRatioM = (double)blockSize / 32;
    if (blockRatioM == 1) return 0;
    int lowerBound = 1;
    int upperBound = 2;
    int temp = 0;
    for (int i = 1; i < NUM_FREE_LISTS - 2; i++) {
        if ((blockRatioM > lowerBound) && (blockRatioM <= upperBound)) {
            return i;
        } else {
            temp = lowerBound;
            lowerBound = upperBound;
            upperBound += temp;
        }
    }
    return (NUM_FREE_LISTS - 2);
}

// Encodes header and footer of a block
static void writeBlock(sf_block *inputBlock, int payloadSize, int blockSize, int alloc, int prevAlloc) {
    size_t header = payloadSize;
    header <<= 32;
    header |= blockSize;
    if (alloc) header |= 8;
    if (prevAlloc) header |= 4;

    // Encode block header
    inputBlock->header = header;

    // Moves pointer to start of next sf_block
    void *ptr = inputBlock;
    ptr = (char*)ptr;
    ptr += blockSize;
    inputBlock = (sf_block*)ptr;

    // Encode block prev_footer
    inputBlock->prev_footer = header;
    return;
}

// Encodes epilogue of heap
static void encodeEpilogue(int prevAlloc) {
    size_t epilogueHeader = 8; // Epilogue with all empty fields except alloc
    void *ptr = sf_mem_end(); // Pointer initialization
    ptr = (char*)ptr; 
    ptr -= 16; // Pointer move to start of epilogue sf_block.prev_footer
    sf_block *epilogue = (sf_block*)ptr;
    if (prevAlloc) epilogueHeader |= 4; 
    epilogue->header = epilogueHeader; // Encode epilogue header
    return;
}

// Returns payload of given header
static size_t findPayload(size_t header) {
    header >>= 32;
    return header;
}

// Returns block size of given header
static size_t findBlockSize(size_t header) {
    size_t size = (int)header;
    size &= 0xfffffff0;
    return size;
}

// Returns allocated bit of given header
static int isAllocated(size_t header) {
    size_t size = (int)header;
    size &= 0x00000008;
    if (size > 0) return 1;
    return 0;
}

// Returns prev_alloc bit of given header
static int isPrevAllocated(size_t header) {
    size_t size = (int)header;
    size &= 0x00000004;
    if (size > 0) return 1;
    return 0;
}

// Splits and creates new block depending on original block size
static void determineSplit(sf_block *suitableBlock, size_t reqBlockSize, size_t payloadSize, int isWilderness, int reallocMod) {
    sf_block *tempBlockPtr = NULL;
    size_t originalHeader = suitableBlock->header; // Preserves header from suitable block
    size_t originalBlockSize = findBlockSize(originalHeader); // Determines block size
    int prevAlloc = isPrevAllocated(originalHeader); // Determines if previous block was allocated

    if (!reallocMod) removeFromFreeList(suitableBlock); // Removes suitable block from free list

    if ((originalBlockSize - reqBlockSize) >= 32) { // Adequate block size for split
        originalBlockSize = originalBlockSize - reqBlockSize; // Original block changes to new size after split
        writeBlock(suitableBlock, payloadSize, reqBlockSize, 1, prevAlloc);
        totalPayloadCalculation(payloadSize);
        totalBlockSize += reqBlockSize;

        // Creates free block after split
        void *ptr = suitableBlock;
        ptr = (char*)ptr;
        ptr += reqBlockSize;
        tempBlockPtr = (sf_block*)ptr;

        // Determines information about next block
        ptr += originalBlockSize;
        sf_block *nextBlock = (sf_block*)ptr;
        sf_block *wildernessHead = &sf_free_list_heads[NUM_FREE_LISTS - 1];
        size_t endBlockSize = originalBlockSize;

        // Coalesce with next block if possible
        if (isAllocated(nextBlock->header) == 0) { 
            endBlockSize += findBlockSize(nextBlock->header);
            if (wildernessHead == nextBlock->body.links.next) isWilderness = 1; // nextBlock is wilderness block
            removeFromFreeList(nextBlock);
        }

        writeBlock(tempBlockPtr, 0, endBlockSize, 0, 1);

        // Add new free block to free lists
        if (isWilderness) {
            addToFreeList(tempBlockPtr, NUM_FREE_LISTS - 1);
        } else {
            int listIndex = determineFreeListIndex(originalBlockSize);
            addToFreeList(tempBlockPtr, listIndex);
        }
    } else { // Inadequate block size for split
        writeBlock(suitableBlock, payloadSize, originalBlockSize, 1, prevAlloc);
        totalPayloadCalculation(payloadSize);
        totalBlockSize += originalBlockSize;
    }
}

// Removes element from free list
static void removeFromFreeList(sf_block *inputBlock) {
    sf_block *nextBlock = inputBlock->body.links.next;
    sf_block *prevBlock = inputBlock->body.links.prev;
    nextBlock->body.links.prev = prevBlock;
    prevBlock->body.links.next = nextBlock;
}

// Adds element to free list
static void addToFreeList(sf_block *inputBlock, int listIndex) {
    sf_block *nextBlock = sf_free_list_heads[listIndex].body.links.next;
    sf_free_list_heads[listIndex].body.links.next = inputBlock;
    inputBlock->body.links.prev = &sf_free_list_heads[listIndex];
    nextBlock->body.links.prev = inputBlock;
    inputBlock->body.links.next = nextBlock;
} 

// Returns 1 if pointer is valid, 0 if invalid
static void verifyPointer(void *ptr) {
    if (ptr == NULL) { // NULL pointer
        sf_errno = EINVAL;
        abort();
    } 
    ptr = (char*)ptr;

    // Determines byte alignment
    void *tempPtr = sf_mem_start();
    tempPtr = (char*)tempPtr;
    tempPtr += 8;
    int remainder = (ptr - tempPtr) % 16;

    // Determines block information
    ptr -= 16;
    sf_block *inputBlock = (sf_block*)ptr;
    size_t blockSize = findBlockSize(inputBlock->header);
    int allocated = isAllocated(inputBlock->header);
    int prevAlloc = isPrevAllocated(inputBlock->header);
    int prevBlockAlloc = isAllocated(inputBlock->prev_footer);

    // Determines header position
    ptr += 8;
    tempPtr += 32;
    int headerDifference = ptr - tempPtr;

    // Determines footer position
    ptr += blockSize;
    tempPtr = sf_mem_end();
    tempPtr = (char*)tempPtr;
    int footerDifference = tempPtr - ptr;
 
    // Input validation
    if (remainder != 8) { // Pointer is not 16-byte aligned
        sf_errno = EINVAL;
        abort();
    } else if (blockSize < 32) { // Block is smaller than minimum size
        sf_errno = EINVAL;
        abort();
    } else if ((blockSize % 16) != 0) { // Block size not multiple of 16
        sf_errno = EINVAL;
        abort();
    } else if (headerDifference < 0) { // Header of block is before first block of heap
        sf_errno = EINVAL;
        abort();
    } else if (footerDifference < 0) { // Footer of block is after last block of heap
        sf_errno = EINVAL;
        abort();
    } else if (allocated == 0) { // Block allocated bit is set to 0
        sf_errno = EINVAL;
        abort();
    } else if ((prevAlloc == 0) && (prevBlockAlloc == 1)) { // Incorrect prev_alloc field
        sf_errno = EINVAL;
        abort();
    }
}

// Adds new allocated block to payload size tracker, determines if new size is max
static void totalPayloadCalculation(size_t payload) {
    totalPayloadSize += payload;
    if (totalPayloadSize > maxAggregatePayload) maxAggregatePayload = totalPayloadSize;
}

void sf_free(void *ptr) {
    verifyPointer(ptr);

    // Determines block information
    ptr = (char*)ptr;
    ptr -= 16;
    void *tempPtr = NULL;
    sf_block *inputBlock = (sf_block*)ptr;
    size_t payloadSize = findPayload(inputBlock->header);
    size_t blockSize = findBlockSize(inputBlock->header);
    int prevAlloc = isPrevAllocated(inputBlock->header);
    int prevBlockAlloc = isAllocated(inputBlock->prev_footer);
    int prevBlockSize = findBlockSize(inputBlock->prev_footer);

    totalPayloadSize -= payloadSize;
    totalBlockSize -= blockSize;

    sf_block *prevBlock = inputBlock;
    size_t endBlockSize = blockSize;

    // Coalesce with previous block if possible
    if (prevAlloc == 0) {
        endBlockSize += prevBlockSize;
        tempPtr = inputBlock;
        tempPtr = (char*)tempPtr;
        tempPtr -= prevBlockSize;
        prevBlock = (sf_block*)tempPtr;
        prevBlockAlloc = isPrevAllocated(prevBlock->header);
        removeFromFreeList(prevBlock);
    }

    tempPtr = inputBlock;
    tempPtr = (char*)tempPtr;
    tempPtr += blockSize;
    sf_block *nextBlock = (sf_block*)tempPtr;
    int isWilderness = 0;

    sf_block *wildernessHead = &sf_free_list_heads[NUM_FREE_LISTS - 1];

    // Coalesce with next block if possible
    if (isAllocated(nextBlock->header) == 0) {
        endBlockSize += findBlockSize(nextBlock->header);
        if (wildernessHead == nextBlock->body.links.next) isWilderness = 1; // nextBlock is wilderness block
        removeFromFreeList(nextBlock);
    } 

    writeBlock(prevBlock, 0, endBlockSize, 0, prevBlockAlloc);

    if (!isWilderness) {
        tempPtr = prevBlock;
        tempPtr += endBlockSize;
        nextBlock = (sf_block*)tempPtr;
        size_t nextBlockPayload = findPayload(nextBlock->header);
        size_t nextBlockSize = findBlockSize(nextBlock->header);
        size_t nextBlockAlloc = isAllocated(nextBlock->header);
        writeBlock(nextBlock, nextBlockPayload, nextBlockSize, nextBlockAlloc, 0);
    }


    if (isWilderness) {
        addToFreeList(prevBlock, NUM_FREE_LISTS - 1);
    } else {
        int listIndex = determineFreeListIndex(endBlockSize);
        addToFreeList(prevBlock, listIndex);
    }

    return;

    abort();
}

void *sf_realloc(void *ptr, size_t rsize) {
    // Verify pointer information
    verifyPointer(ptr);

    // Free the block if rsize is 0
    if (rsize == 0) {
        sf_free(ptr);
        return NULL;
    }

    // Stores original pointer for future use
    void *originalPtr = ptr;
    
    // Determines information about original block
    ptr = (char*)ptr;
    ptr -= 16; // Moves ptr to access sf_block
    sf_block *originalBlock = (sf_block*)ptr;
    size_t originalPayload = findPayload(originalBlock->header); // Finds original payload size
    size_t originalBlockSize = findBlockSize(originalBlock->header); // Finds original block size
    size_t originalPrevAlloc = isPrevAllocated(originalBlock->header); // Finds original prev_alloc bit
    size_t reqBlockSize = ((rsize + 31) / 16) * 16; // Finds new required block size
    void *newPtr = originalBlock;

    // Determines whether reallocating to larger or smaller block
    if (rsize == originalPayload) { // Return same block
        return originalPtr;
    } else if (reqBlockSize > originalBlockSize) { // Allocating larger block
        // Allocates new block and copies data
        newPtr = sf_malloc(rsize);
        memcpy(newPtr, originalPtr, originalPayload);
        // Frees old block
        sf_free(originalPtr);
        return newPtr;
    } else { // Allocating smaller block
        if ((originalBlockSize - reqBlockSize) > 32) { // Split blocks, return original pointer
            determineSplit(originalBlock, reqBlockSize, rsize, 0, 1);
            return originalPtr;
        } else { // Update header and return original pointer
            writeBlock(originalBlock, rsize, originalBlockSize, 1, originalPrevAlloc);
            return originalPtr;
        }
    }

    abort();
}

double sf_fragmentation() {
    if (totalPayloadSize == 0) return 0;
    return (totalPayloadSize / totalBlockSize);
    abort();
}

double sf_utilization() {
    if (firstMallocFlag == 1) return 0;
    void *startPtr = sf_mem_start();
    startPtr = (char*)startPtr;
    void *endPtr = sf_mem_end();
    endPtr = (char*)endPtr;

    double heapSize = endPtr - startPtr;

    return (maxAggregatePayload / heapSize);

    abort();
}

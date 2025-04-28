#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    " Mother Hen",
    /* First member's full name */
    " Bryce Strickland ",
    /* First member's email address */
    " brst8941@colorado.edu ",
    /* Second member's full name (leave blank if none) */
    " Nika Shafranov",
    /* Second member's email address (leave blank if none) */
    " nish1367@colorado.edu "
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


// My additional Macros
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE (1<<12) /* Page size in bytes */

#define LISTLIMIT     16 /* Optimized number of segregated lists */
#define REALLOC_BUFFER  (1<<7) /* Reallocation buffer */

static inline int MAX(int x, int y) { /* Maximum of two numbers */
    return x > y ? x : y;
}

static inline int MIN(int x, int y) { /* Minimum of two numbers */
    return x < y ? x : y;
}

static inline size_t PACK(size_t size, int alloc) {
    return ((size) | (alloc & 0x1));
}

/* Read and write a word at address p */
static inline size_t GET(void *p) {
    return  *(size_t *)p;
}

/* Get the reallocation tag */
static inline size_t GET_TAG(void *p) {
    return GET(p) & 0x2;
}

/* Remove reallocation tag */
static inline size_t REMOVE_RATAG(void *p) {
    return GET(p) & ~0x2;
}

/* Set reallocation tag */
static inline size_t SET_RATAG(void *p) {
    return GET(p) | 0x2;
}

/* Put value at address p, preserving reallocation tag */
static inline void PUT(void *p, size_t val) {
    *((size_t *)p) = (val | GET_TAG(p));
}

/* Put value at address p, clearing reallocation tag */
static inline void PUT_NOTAG(void *p, size_t val) {
    *((size_t *)p) = val;
}

/* Store pointer for free blocks */
static inline void SET_PTR(void *p, void *ptr) {
    *((unsigned int *)p) = (unsigned int)(ptr);
}

/* Read the size from address p */
static inline size_t GET_SIZE(void *p) {
    return GET(p) & ~0x7;
}

/* Read the allocation bit from address p */
static inline int GET_ALLOC(void *p) {
    return GET(p) & 0x1;
}

/* Address of block's header and footer */
static inline void *HDRP(void *bp) {
    return ((char *)bp) - WSIZE;
}

static inline void *FTRP(void *bp) {
    return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

/* Address of next and previous blocks */
static inline void *NEXT_BLKP(void *ptr) {
    return ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE)));
}

static inline void* PREV_BLKP(void *ptr) {
    return ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DSIZE)));
}

/* Address of free block's predecessor and successor entries */
static inline void* PRED_PTR(void *ptr) {
    return ((char *)(ptr));
}

static inline void* SUCC_PTR(void *ptr) {
    return ((char*)(ptr) + WSIZE);
}

/* Address of free block's predecessor and successor on the segregated list */
static inline void* PRED(void *ptr) {
    return (*(char **)(ptr));
}

static inline void* SUCC(void *ptr) {
    return (*(char **)(SUCC_PTR(ptr)));
}

/* Global variable for segregated free lists */
void *segregated_free_lists[LISTLIMIT];

/* Function declarations */
static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);
static int get_list_index(size_t size);

/* Optimized function to determine the segregated list index based on size */
static int get_list_index(size_t size) {
    if (size <= 16) return 0;           // Small blocks (16 bytes or less)
    else if (size <= 32) return 1;      // 32 bytes or less
    else if (size <= 64) return 2;      // 64 bytes or less
    else if (size <= 128) return 3;     // 128 bytes or less
    else if (size <= 256) return 4;     // 256 bytes or less
    else if (size <= 512) return 5;     // 512 bytes or less
    else if (size <= 1024) return 6;    // 1KB or less
    else if (size <= 2048) return 7;    // 2KB or less
    else if (size <= 4096) return 8;    // 4KB or less
    else if (size <= 8192) return 9;    // 8KB or less
    else if (size <= 16384) return 10;  // 16KB or less
    else if (size <= 32768) return 11;  // 32KB or less
    else if (size <= 65536) return 12;  // 64KB or less
    else if (size <= 131072) return 13; // 128KB or less
    else if (size <= 262144) return 14; // 256KB or less
    else return 15;                     // Larger blocks
}

/* Optimized extend_heap function */
static void *extend_heap(size_t size) {
    void *ptr;   /* Pointer to newly allocated memory */
    size_t asize;  /* Adjusted size */
    
    asize = ALIGN(size); /* Maintain alignment */
    
    /* Extend the heap */
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    /* Set headers and footer */
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0)); /* Free block header */
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0)); /* Free block footer */
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));  /* Epilogue header */
    
    /* Insert new block into appropriate list */
    insert_node(ptr, asize);
    
    /* Coalesce if the previous block was free */
    return coalesce(ptr);
}

/* Optimized insert_node function with address-ordered insertion */
static void insert_node(void *ptr, size_t size) {
    int list = get_list_index(size);
    void *search_ptr, *insert_ptr = NULL;
    
    /* Address-ordered insertion to improve cache locality */
    search_ptr = segregated_free_lists[list];
    while ((search_ptr != NULL) && (ptr > search_ptr)) {
        insert_ptr = search_ptr;
        search_ptr = PRED(search_ptr);
    }
    
    /* Set predecessor and successor pointers */
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            /* Insert in the middle of the list */
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            /* Insert at the beginning of the list */
            SET_PTR(PRED_PTR(ptr), search_ptr);
            SET_PTR(SUCC_PTR(search_ptr), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    } else {
        if (insert_ptr != NULL) {
            /* Insert at the end of the list */
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), insert_ptr);
            SET_PTR(PRED_PTR(insert_ptr), ptr);
        } else {
            /* Create a new list */
            SET_PTR(PRED_PTR(ptr), NULL);
            SET_PTR(SUCC_PTR(ptr), NULL);
            segregated_free_lists[list] = ptr;
        }
    }
}

/* Optimized delete_node function */
static void delete_node(void *ptr) {
    int list = get_list_index(GET_SIZE(HDRP(ptr)));
    
    /* Update pointers of adjacent blocks */
    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            /* Middle block, update both sides */
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));
        } else {
            /* Last block in list */
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            segregated_free_lists[list] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr) != NULL) {
            /* First block in list */
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);
        } else {
            /* Only block in list */
            segregated_free_lists[list] = NULL;
        }
    }
}

/* Optimized coalesce function */
static void *coalesce(void *ptr) {
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    
    /* Check if previous block has reallocation tag set */
    if (GET_TAG(HDRP(PREV_BLKP(ptr))))
        prev_alloc = 1;
    
    /* Four cases for coalescing */
    if (prev_alloc && next_alloc) {
        /* Case 1: Both adjacent blocks are allocated */
        return ptr;
    } else if (prev_alloc && !next_alloc) {
        /* Case 2: Only next block is free */
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        /* Case 3: Only previous block is free */
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    } else {
        /* Case 4: Both adjacent blocks are free */
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    
    /* Insert coalesced block into appropriate list */
    insert_node(ptr, size);
    
    return ptr;
}

/* Optimized place function */
static void *place(void *ptr, size_t asize) {
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;
    
    /* Remove block from list */
    delete_node(ptr);
    
    /* Decide whether to split the block */
    if (remainder <= 2 * DSIZE) {
        /* Don't split - too small */
        PUT(HDRP(ptr), PACK(ptr_size, 1));
        PUT(FTRP(ptr), PACK(ptr_size, 1));
    } else if (asize >= 96) {
        /* Split with remainder at front (front-fit) for large requests */
        PUT(HDRP(ptr), PACK(remainder, 0));
        PUT(FTRP(ptr), PACK(remainder, 0));
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        insert_node(ptr, remainder);
        return NEXT_BLKP(ptr);
    } else {
        /* Split with remainder at back (back-fit) for smaller requests */
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        insert_node(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
}

/* Optimized mm_init function */
int mm_init(void) {
    int list;
    char *heap_start;
    
    /* Initialize segregated free lists */
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }
    
    /* Allocate memory for initial empty heap */
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;
    
    PUT_NOTAG(heap_start, 0);                            /* Alignment padding */
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    /* Extend the empty heap */
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    
    return 0;
}

/* Optimized mm_malloc function with best-fit strategy */
void *mm_malloc(size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *ptr = NULL;  /* Pointer */
    int list;          /* List index */
    
    /* Ignore size 0 cases */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment requirements */
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size + DSIZE);
    }
    
    /* Find best fit using optimized list selection */
    int start_list = get_list_index(asize);
    size_t min_size = (size_t)-1;  /* Initialize to max value */
    void *best_ptr = NULL;
    
    /* Search through appropriate lists */
    for (list = start_list; list < LISTLIMIT; list++) {
        ptr = segregated_free_lists[list];
        while (ptr != NULL) {
            size_t block_size = GET_SIZE(HDRP(ptr));
            
            /* Check if block fits and is better than current best fit */
            if ((asize <= block_size) && 
                (block_size < min_size) && 
                !GET_TAG(HDRP(ptr))) {
                min_size = block_size;
                best_ptr = ptr;
                
                /* If exact fit found, stop searching */
                if (min_size == asize)
                    break;
            }
            ptr = PRED(ptr);
        }
        
        /* If fit found, stop searching */
        if (best_ptr != NULL)
            break;
    }
    
    /* If no fit found, extend heap */
    if (best_ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
        best_ptr = ptr;
    }
    
    /* Place block */
    ptr = place(best_ptr, asize);
    
    return ptr;
}

/* Optimized mm_free function */
void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));
    
    /* Clear reallocation tag on next block */
    void *next_block = HDRP(NEXT_BLKP(ptr));
    size_t next_value = GET(next_block);
    PUT_NOTAG(next_block, next_value & ~0x2);
    
    /* Mark block as free */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    /* Insert block into appropriate list */
    insert_node(ptr, size);
    
    /* Coalesce free blocks */
    coalesce(ptr);
}

/* Optimized mm_realloc function */
void *mm_realloc(void *ptr, size_t size) {
    void *new_ptr = ptr;    /* Pointer to be returned */
    size_t new_size = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */
    
    /* Ignore invalid block size */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment requirements */
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size + DSIZE);
    }
    
    /* Add overhead requirements to block size */
    new_size += REALLOC_BUFFER;
    
    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;
    
    /* Check if current block can satisfy the request */
    if (block_buffer >= 0) {
        /* Current block is large enough */
        if (block_buffer < 2 * REALLOC_BUFFER) {
            /* Set reallocation tag if overhead drops below threshold */
            PUT(HDRP(NEXT_BLKP(ptr)), SET_RATAG(HDRP(NEXT_BLKP(ptr))));
        }
        return ptr;
    }
    
    /* Try to coalesce with adjacent blocks */
    
    /* Check if both previous and next blocks are free */
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) && 
        !GET_ALLOC(HDRP(PREV_BLKP(ptr))) && 
        !GET_TAG(HDRP(PREV_BLKP(ptr)))) {
        
        size_t combined_size = GET_SIZE(HDRP(ptr)) + 
                            GET_SIZE(HDRP(NEXT_BLKP(ptr))) + 
                            GET_SIZE(HDRP(PREV_BLKP(ptr)));
        
        if (combined_size >= new_size) {
            delete_node(NEXT_BLKP(ptr));
            delete_node(PREV_BLKP(ptr));
            
            new_ptr = PREV_BLKP(ptr);
            
            /* Move data to new location */
            memmove(new_ptr, ptr, GET_SIZE(HDRP(ptr)) - DSIZE);
            
            PUT_NOTAG(HDRP(new_ptr), PACK(combined_size, 1));
            PUT_NOTAG(FTRP(new_ptr), PACK(combined_size, 1));
            
            return new_ptr;
        }
    }
    
    /* Check if next block is free or epilogue */
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
        remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
        
        /* If combined size is insufficient, extend heap */
        if (remainder < 0) {
            extendsize = MAX(-remainder, CHUNKSIZE);
            if (extend_heap(extendsize) == NULL)
                return NULL;
            remainder += extendsize;
        }
        
        /* Delete next block from free list */
        delete_node(NEXT_BLKP(ptr));
        
        /* Update header/footer of current block */
        PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1));
        PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1));
    } else {
        /* Allocate new block */
        new_ptr = mm_malloc(new_size - DSIZE);
        
        /* Copy data from old block to new block */
        memcpy(new_ptr, ptr, MIN(size, new_size));
        
        /* Free old block */
        mm_free(ptr);
    }
    
    /* Tag next block if block overhead drops below threshold */
    if (GET_SIZE(HDRP(new_ptr)) - new_size < 2 * REALLOC_BUFFER)
        PUT(HDRP(NEXT_BLKP(new_ptr)), SET_RATAG(HDRP(NEXT_BLKP(new_ptr))));
    
    return new_ptr;
}
/*
 * mm-naive.c - 가장 빠르지만 메모리 효율이 가장 낮은 malloc 패키지입니다.
 * 이 단순 접근 방식에서는 brk 포인터를 단순히 증가시켜 블록을 할당합니다.
 * 블록은 순수한 페이로드입니다. 헤더나 푸터가 없습니다. 블록은 병합되거나 재사용되지 않습니다.
 * realloc은 mm_malloc과 mm_free를 사용하여 직접 구현됩니다.
 *
 * 참고: 이 헤더 주석을 해결책에 대한 간략한 설명을 제공하는 자체 헤더 주석으로 바꾸세요.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "5team",
    /* First member's full name */
    "Kim Taeyong",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};


// 기본 상수
#define WSIZE 4                // 글자, 헤더, 풋터 크기 4byte
#define DSIZE 8                // 더블(부동소수점) 글자 크기 8byte
#define CHUNKSIZE (1<<12)      // 힙 확장을 위한 기본 크기(초기의 빈 블록의 크기)

// 매크로
#define MAX(x, y)  ((x) > (y) ? (x) : (y))

// size와 할당 비트를 결합, header와 footer에 저장할 값
#define PACK(size, alloc)  ((size) | (alloc))

// p가 참조하는 워드 반환(포인터라서 직접 역참조 불가능 -> 타입 캐스팅)
#define GET(p)        (*(unsigned int *)(p))
// p에 val 저장
#define PUT(p, val)   (*(unsigned int *)(p) = (val))

// 사이즈 (~0x7: ...11111000, '&' 연산으로 뒤에 세자리 없어짐)
#define GET_SIZE(p)   (GET(p) & ~0x7)
// 할당 상태
#define GET_ALLOC(p)  (GET(p) & 0x1)

// Header 포인터
#define HDRP(bp)      ((char *)(bp) - WSIZE)
// Footer 포인터 (Header의 정보를 참조해서 가져오기 때문에, Header의 정보를 변경했다면 변경된 위치의 Footer가 반환됨에 유의)
#define FTRP(bp)      ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// 다음 블록의 포인터
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// 이전 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define GET_SUCC(bp) (*(void **)((char *)(bp) + WSIZE)) // 다음 가용 블록의 주소
#define GET_PRED(bp) (*(void **)(bp))                   // 이전 가용 블록의 주소

static void *free_listp = NULL;
// 함수 선언 (프로토타입만 먼저 선언해줌)
static void add_free_block(void *bp);
static void splice_free_block(void *bp);

/*
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc) // 모두 할당된 경우
    {
        add_free_block(bp); // free_list에 추가
        return bp;          // 블록의 포인터 반환
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        splice_free_block(NEXT_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        splice_free_block(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        splice_free_block(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    add_free_block(bp); // 현재 병합한 가용 블록을 free_list에 추가
    return bp;          // 병합한 가용 블록의 포인터 반환
}
    
*/

static void *coalesce(void *bp)
    {
        size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
        size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

        if (prev_alloc && next_alloc) // 모두 할당된 경우
        {
            add_free_block(bp); // free_list에 추가
            return bp;          // 블록의 포인터 반환
        }
        else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
        {
            splice_free_block(NEXT_BLKP(bp)); // 가용 블록을 free_list에서 제거
            size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
            PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
            PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
            add_free_block(bp);
        }
        else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
        {
            size += GET_SIZE(HDRP(PREV_BLKP(bp)));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
            PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
            bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
        }
        else // 이전 블록과 다음 블록 모두 빈 경우
        {
            splice_free_block(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
            size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
            PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
            bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
        }
        return bp; // 병합한 가용 블록의 포인터 반환
    }

// 힙 확장: 새 가용 블록으로 힙을 확장한다.
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 더블 워드 정렬 유지
    // size: 확장할 크기
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;   // 더블워드의 가장 가까운 배수로 반올림(홀수면 1 더해서 곱한다)
    if ((long)(bp = mem_sbrk(size)) == -1)                      // 힙 확장
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));           // 새 빈 블록 헤더 초기화
    PUT(FTRP(bp), PACK(size, 0));           // 새 빈 블록 풋터 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   //  에필로그 블록 헤더 초기화

    return coalesce(bp);     // 병합 후 coalesce 함수에서 리턴된 블록 포인터 반환
}

/////////////////
// 검색 후 가용블록 반환하기 (First fit)
// 가용 리스트를 순차적으로 검색해서, 요청 크기 이상의 가용 블록을 찾아 반환한다
static void *find_fit(size_t asize)
{
    void *bp = free_listp;
    while (bp != NULL) // 다음 가용 블럭이 있는 동안 반복
    {
        if ((asize <= GET_SIZE(HDRP(bp)))) // 적합한 사이즈의 블록을 찾으면 반환
            return bp;
        bp = GET_SUCC(bp); // 다음 가용 블록으로 이동
    }
    return NULL;
}

/*
// 효과적으로 분할하기
// 블록을 할당할 때, 남는 공간이 충분하면 블록을 분할(split) 하고, 그렇지 않으면 그냥 전체 블록을 할당한다
static void place(void *bp, size_t asize)
    {
        splice_free_block(bp); // free_list에서 해당 블록 제거

        size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

        if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
        {
            PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
            PUT(FTRP(bp), PACK(asize, 1));

            PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
            PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
            add_free_block(NEXT_BLKP(bp)); // 남은 블록을 free_list에 추가
        }
        else
        {
            PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
            PUT(FTRP(bp), PACK(csize, 1));
        }
    }
*/

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
    {
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp); // 다음 블록으로 이동

        PUT(HDRP(bp), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
        PUT(FTRP(bp), PACK((csize - asize), 0));

        GET_SUCC(bp) = GET_SUCC(PREV_BLKP(bp)); // 루트였던 블록의 PRED를 추가된 블록으로 연결

        if (PREV_BLKP(bp) == free_listp) 
        {
            free_listp = bp;
        }
        else
        {
            GET_PRED(bp) = GET_PRED(PREV_BLKP(bp));
            GET_SUCC(GET_PRED(PREV_BLKP(bp))) = bp;
        }

        if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
            GET_PRED(GET_SUCC(bp)) = bp;
    }
    else
    {
        splice_free_block(bp);
        PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

    // 가용 리스트에서 bp에 해당하는 블록을 제거하는 함수
static void splice_free_block(void *bp)
{
    if (bp == free_listp) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        free_listp = GET_SUCC(free_listp); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    GET_SUCC(GET_PRED(bp)) = GET_SUCC(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
        GET_PRED(GET_SUCC(bp)) = GET_PRED(bp);
}

/*
// 가용 리스트의 맨 앞에 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    GET_SUCC(bp) = free_listp;     // bp의 SUCC은 루트가 가리키던 블록
    if (free_listp != NULL)        // free list에 블록이 존재했을 경우만
        GET_PRED(free_listp) = bp; // 루트였던 블록의 PRED를 추가된 블록으로 연결
    free_listp = bp;               // 루트를 현재 블록으로 변경
}*/

// 가용 리스트에서 주소 오름차순에 맞게 현재 블록을 추가하는 함수
static void add_free_block(void *bp)
{
    void *currentp = free_listp;
    if (currentp == NULL)
    {
        free_listp = bp;
        GET_SUCC(bp) = NULL;
        return;
    }

    while (currentp < bp) // 검사중인 주소가 추가하려는 블록의 주소보다 작을 동안 반복
    {
        if (GET_SUCC(currentp) == NULL || GET_SUCC(currentp) > bp)
            break;
        currentp = GET_SUCC(currentp);
    }

    GET_SUCC(bp) = GET_SUCC(currentp); // 루트였던 블록의 PRED를 추가된 블록으로 연결
    GET_SUCC(currentp) = bp;           // bp의 SUCC은 루트가 가리키던 블록
    GET_PRED(bp) = currentp;           // bp의 SUCC은 루트가 가리키던 블록

    if (GET_SUCC(bp) != NULL) // 다음 가용 블록이 있을 경우만
    {
        GET_PRED(GET_SUCC(bp)) = bp;
    }
}

//////////////

// mm_init - initialize the malloc package.
// 힙 생성하기: 패딩+프롤로그 헤더+프롤로그 풋터+에필로그 풋터를 담기위해 8워드 크기합을 구성함
// 생성 후 CHUNKSIZE만큼 추가 메모리를 요청해 힙의 크기를 확장
int mm_init(void)
{
    // 초기 힙 생성
    if ((free_listp = mem_sbrk(8 * WSIZE)) == (void *)-1) // 8워드 크기의 힙 생성, free_listp에 힙의 시작 주소값 할당(가용 블록만 추적)
        return -1;
    PUT(free_listp, 0);                                // 정렬 패딩
    PUT(free_listp + (1 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Header
    PUT(free_listp + (2 * WSIZE), PACK(2 * WSIZE, 1)); // 프롤로그 Footer
    PUT(free_listp + (3 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 헤더
    PUT(free_listp + (4 * WSIZE), NULL);               // 이전 가용 블록의 주소
    PUT(free_listp + (5 * WSIZE), NULL);               // 다음 가용 블록의 주소
    PUT(free_listp + (6 * WSIZE), PACK(4 * WSIZE, 0)); // 첫 가용 블록의 푸터
    PUT(free_listp + (7 * WSIZE), PACK(0, 1));         // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄

    free_listp += (4 * WSIZE); // 첫번째 가용 블록의 bp

    // 힙을 CHUNKSIZE bytes로 확장
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

// mm_malloc - Allocate a block by incrementing the brk pointer.
// Always allocate a block whose size is a multiple of the alignment.
// 가용 블록 할당하기
// brk 포인터를 증가시켜 블록을 할당합니다. 항상 정렬 크기의 배수인 블록을 할당합니다.
void *mm_malloc(size_t size)
{
    size_t asize;           // 요청된 크기를 조정한 블록 크기 (payload + overhead 포함)
    size_t extendsize;      // heap을 확장할 사이즈
    char *bp;               // 새로 할당할 블록 포인터

    // 잘못된 요청 처리: size가 0이면 NULL 반환
    if(size == 0)
        return NULL;

    // 요청 크기 조정 (payload + header/footer 포함, alignment 맞추기)
    if (size <= DSIZE)        // 8바이트 이하 시
        asize = 2*DSIZE;      // 최소 블록 크기 16바이트 할당 (헤더 4 + 푸터 4 + 저장공간 8)
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);     // size에 overhead 추가하고, DSIZE 단위로 8의 배수로 올림 (align)

    // Step 1: 가용 리스트에서 알맞은 블록 찾기
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);     // 블록을 할당하고
        return bp;            // 포인터 반환
    }

    // Step 2: 가용 블록이 없으면 힙을 확장
    extendsize = MAX(asize, CHUNKSIZE);     // 최소 CHUNKSIZE만큼은 확장
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;    // 확장 실패시 NULL 반환
    
    place(bp, asize);   // 새로 확장한 블록에 메모리 배치
    return bp;          // 새 블록 포인터 반환
}


// mm_free - Freeing a block does nothing.
// 블록 반환하기
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));  // 현재 블록(bp)의 헤더를 읽어서 블록 크기(size)를 가져옴

    PUT(HDRP(bp), PACK(size, 0));      // 블록의 헤더(Header) 정보를 업데이트: size 그대로, 할당 비트(allocation bit)는 0 (free 상태)
    PUT(FTRP(bp), PACK(size, 0));      // 블록의 푸터(Footer) 정보도 업데이트: size 그대로, 할당 비트는 0 (free 상태)
    coalesce(bp);                      // 인접한 가용 블록들과 병합(Coalesce) 시도
}


// mm_realloc - Implemented simply in terms of mm_malloc and mm_free
// 재할당 블록 재할당하기
// 기존 블록 내용을 새 블록에 복사한 후 기존 블록을 해제, 새 포인터 반환
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;    // 기존 블록 포인터
    void *newptr;          // 새로 할당받을 블록 포인터
    size_t copySize;       // 복사할 데이터 크기

    // Step 1: 새 크기만큼 메모리를 할당
    newptr = mm_malloc(size);
    if (newptr == NULL)    // 메모리 할당 실패 시 NULL 반환
        return NULL;       

    // Step 2: 기존 블록의 크기 읽기
    copySize = GET_SIZE(HDRP(oldptr));

    // Step 3: 복사할 크기를 요청 크기로 조정 (원래 블록이 더 크면 size까지만 복사)
    if (size < copySize)
        copySize = size;

    // Step 4: 데이터 복사
    memcpy(newptr, oldptr, copySize);

    // Step 5: 기존 블록 반환 (free)
    mm_free(oldptr);

    return newptr;         // 새 블록 포인터 반환
}
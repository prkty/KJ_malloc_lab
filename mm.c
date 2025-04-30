#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    " Team 5",
    /* First member's full name */
    " Unknown ",
    /* First member's email address */
    " none@colorado.edu ",
    /* Second member's full name (leave blank if none) */
    " None",
    /* Second member's email address (leave blank if none) */
    " None@colorado.edu "
};

/* 싱글 word (4) or 더블 word (8) alignment */
#define ALIGNMENT 8
/* size를 8의 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define WSIZE     4            // 글자, 풋터, 헤더 사이즈 (bytes)
#define DSIZE     8            // 더블 글자 사이즈 (bytes)
#define INITCHUNKSIZE (1<<6)   // 초기 힙 확장 크기
#define CHUNKSIZE (1<<12)      // 힙 확장 단위 (4096바이트 = 1페이지)
#define LISTLIMIT     16       // 세분화 리스트 개수
#define REALLOC_BUFFER  (1<<7) // realloc 시 버퍼 크기

// 최대/최소 함수
static inline int MAX(int x, int y) { /* 최대 2개의 숫자 */
    return x > y ? x : y;
}
static inline int MIN(int x, int y) { /* 최소 2개의 숫자 */
    return x < y ? x : y;
}

// 블록 헤더/푸터 값 만들기
static inline size_t PACK(size_t size, int alloc) {
    return ((size) | (alloc & 0x1));
}

// 주소 p에서 값 읽기
static inline size_t GET(void *p) {
    return  *(size_t *)p;
}

// 주소 p에 값 쓰기 (태그 보존)
/*static inline void PUT( void *p, size_t val)
{
    (*((size_t *)p) = val) | GET_TAG(p);
} */

// 주소 p에 값 쓰기 (태그 제거)
static inline void PUT_NOTAG (void *p, size_t val){
  *((size_t *)p) = val;
}

// 태그 처리 매크로
static inline size_t REMOVE_RATAG(void *p){
    return GET(p) & 0x2;
}
static inline size_t SET_RATAG(void *p){
    return GET(p) | 0x2;
}


// 재할당 비트 보존
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))


// free 블록에 대한 전임자 또는 후임자 포인터를 저장합니다.
/*static inline void SET_PTR(void *p, size_t ptr){
     *((size_t *)p) = (size_t ptr);
}*/
#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

// 주소 p에서 크기와 할당 비트를 읽습니다.
// 블록 사이즈 및 상태 정보
static inline size_t GET_SIZE( void *p )  {
    return GET(p) & ~0x7;
}
static inline int GET_ALLOC( void *p  ) {
    return GET(p) & 0x1;
}
static inline size_t GET_TAG( void *p )  {
    return GET(p) & 0x2;
}

//#define GET_TAG(p)   (GET(p) & 0x2)

// 블록 포인터에서 헤더/푸터 주소 계산
static inline void *HDRP(void *bp) {
    return ( (char *)bp) - WSIZE;
}
static inline void *FTRP(void *bp) {
    return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}


// (물리적으로) 다음 및 이전 블록의 주소
// 다음/이전 블록 주소 계산
static inline void *NEXT_BLKP(void *ptr) {
    return  ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE)));
}
static inline void* PREV_BLKP(void *ptr){
    return  ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DSIZE)));
}

// 가용 리스트 연결 포인터
// 자유 블록의 선행 및 후속 항목 주소
static inline void* PRED_PTR(void *ptr){
    return ((char *)(ptr));
}
static inline void* SUCC_PTR(void *ptr){
    return ((char*)(ptr) + WSIZE);
}

// 분리된 목록에서 자유 블록의 선행 및 후속 블록의 주소
static inline void* PRED(void *ptr){
    return (*(char **)(ptr));
}
static inline void* SUCC(void *ptr){
    return (*(char **)(SUCC_PTR(ptr)));
}


// 추가 매크로 종료


// 세분화 리스트 배열
void *segregated_free_lists[LISTLIMIT]; /* 분리된 자유 목록에 대한 포인터 배열 */


// 내부 함수 선언
static void *extend_heap(size_t size);           // 힙 확장 함수
static void *coalesce(void *ptr);                // 인접 블록 병합 함수
static void *place(void *ptr, size_t asize);     // 블록 할당 및 분할 함수
static void insert_node(void *ptr, size_t size); // 블록 리스트 삽입
static void delete_node(void *ptr);              // 블록 리스트 삭제

//////////////////////////////////////// Helper functions //////////////////////////////////////////////////////////

/* 크기에 따라 분리된 목록 인덱스를 결정하기 위한 최적화된 기능 */
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

/*
 * extend_heap - 시스템 콜을 통해 힙 영역을 확장하고, 새로 확장된 블록을 적절한 리스트에 삽입합니다.
 */
static void *extend_heap(size_t size)
{
    void *ptr;               // 새로 할당된 메모리의 포인터
    size_t asize;            // 정렬된 블록 크기

    asize = ALIGN(size);     // 정렬 단위에 맞춰 블록 크기 조정

    // 힙 확장 시도. 실패하면 NULL 반환
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    // 새로 확장된 블록에 header/footer 세팅 (free 상태)
    PUT_NOTAG(HDRP(ptr), PACK(asize, 0));           // 헤더: size, alloc = 0
    PUT_NOTAG(FTRP(ptr), PACK(asize, 0));           // 푸터: size, alloc = 0
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));    // 에필로그 헤더 추가

    insert_node(ptr, asize);    // 새로운 블록을 적절한 리스트에 삽입

    return coalesce(ptr);       // 인접 블록과 병합하여 반환
}

/*
 * insert_node - 새로운 free 블록 포인터를 해당 크기 그룹의 세분화 리스트에 삽입한다.
 *               각 리스트는 2^n ~ 2^(n+1)-1 바이트 범위를 커버하며,
 *               블록들은 주소 오름차순으로 정렬된다.
 */
static void insert_node(void *ptr, size_t size) {
    int list = 0;                    // 삽입할 세분화 리스트 인덱스
    void *search_ptr = ptr;          // 리스트 탐색에 사용할 포인터
    void *insert_ptr = NULL;         // 삽입할 위치의 이전 블록 포인터

    // 블록 크기에 따라 적절한 리스트를 선택 (2^n 단위로 크기 그룹 분류)
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;                  // size를 2로 나누면서 list 인덱스를 증가
        list++;
    }

    // 선택된 리스트에서 현재 블록의 크기보다 큰 블록을 찾기 위해 순회
    search_ptr = segregated_free_lists[list]; // 리스트의 헤드부터 시작
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;              // 이전 블록 저장
        search_ptr = PRED(search_ptr);        // 이전 포인터로 이동하며 탐색
    }

    // 탐색 결과에 따라 블록 삽입 (포인터 설정)
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            // 중간에 삽입할 경우 (앞뒤 모두 존재)
            SET_PTR(PRED_PTR(ptr), search_ptr);         // ptr의 이전을 search_ptr로 설정
            SET_PTR(SUCC_PTR(search_ptr), ptr);         // search_ptr의 다음을 ptr로 설정
            SET_PTR(SUCC_PTR(ptr), insert_ptr);         // ptr의 다음을 insert_ptr로 설정
            SET_PTR(PRED_PTR(insert_ptr), ptr);         // insert_ptr의 이전을 ptr로 설정
        } else {
            // 리스트의 맨 앞에 삽입할 경우
            SET_PTR(PRED_PTR(ptr), search_ptr);         // ptr의 이전을 search_ptr로 설정
            SET_PTR(SUCC_PTR(search_ptr), ptr);         // search_ptr의 다음을 ptr로 설정
            SET_PTR(SUCC_PTR(ptr), NULL);               // ptr의 다음은 NULL
            segregated_free_lists[list] = ptr;          // 리스트 헤드를 ptr로 갱신
        }
    } else {
        if (insert_ptr != NULL) {
            // 리스트의 맨 뒤에 삽입할 경우
            SET_PTR(PRED_PTR(ptr), NULL);               // 이전 없음
            SET_PTR(SUCC_PTR(ptr), insert_ptr);         // 다음은 insert_ptr
            SET_PTR(PRED_PTR(insert_ptr), ptr);         // insert_ptr의 이전은 ptr
        } else {
            // 리스트가 비어있는 경우
            SET_PTR(PRED_PTR(ptr), NULL);               // 이전 없음
            SET_PTR(SUCC_PTR(ptr), NULL);               // 다음 없음
            segregated_free_lists[list] = ptr;          // 리스트 헤드로 설정
        }
    }

    return;
}
/*
해당 함수는 크기별로 분리된 free 리스트 중 적절한 곳을 선택하고, 해당 리스트 안에서 주소 기준 오름차순 정렬을 유지하며 블록을 삽입합니다.
각 블록은 pred, succ 포인터를 이용해 양방향 연결되어 있습니다.
*/

/*
 * delete_node: 세분화 리스트에서 주어진 블록 포인터를 제거하고
 *              연결된 이전/다음 포인터를 조정하거나 리스트 헤드를 재설정한다.
 */

// delete_node - 주어진 free 블록을 세분화 리스트에서 제거한다.
static void delete_node(void *ptr) {
    int list = 0;                                // 리스트 인덱스
    size_t size = GET_SIZE(HDRP(ptr));           // 삭제할 블록의 크기 추출

    // 블록 크기에 따라 알맞은 리스트 인덱스를 선택
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;                              // 크기를 2로 나누면서 리스트 이동
        list++;
    }

    // 이전 노드가 존재할 경우
    if (PRED(ptr) != NULL) {
        if (SUCC(ptr) != NULL) {
            // 앞뒤 모두 존재 → 중간 노드
            SET_PTR(SUCC_PTR(PRED(ptr)), SUCC(ptr));  // 이전 블록의 다음 포인터를 다음 블록으로 설정
            SET_PTR(PRED_PTR(SUCC(ptr)), PRED(ptr));  // 다음 블록의 이전 포인터를 이전 블록으로 설정
        } else {
            // 다음 노드가 없을 경우 → 마지막 노드
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);       // 이전 블록의 다음 포인터를 NULL로 설정
            segregated_free_lists[list] = PRED(ptr);  // 리스트의 헤드를 이전 블록으로 갱신
        }
    } else {
        if (SUCC(ptr) != NULL) {
            // 이전 노드가 없고 다음 노드는 있음 → 첫 번째 노드
            SET_PTR(PRED_PTR(SUCC(ptr)), NULL);       // 다음 블록의 이전 포인터를 NULL로 설정
        } else {
            // 이전, 다음 모두 없음 → 리스트에 유일한 노드
            segregated_free_lists[list] = NULL;       // 리스트 헤드를 NULL로 설정
        }
    }

    return;
}
/*
이 함수는 주어진 블록을 세분화된 가용 리스트에서 제거합니다.
pred, succ 포인터를 적절히 조정하여 양방향 연결 리스트의 무결성을 유지합니다.
리스트의 첫 번째, 마지막, 중간, 유일 노드에 대해 각각 올바르게 처리합니다.
*/

/*
 * coalesce - 인접한 free 블록을 병합한다. 병합 후 새 블록을 적절한 리스트에 삽입한다.
 *            이전 블록에 재할당 태그가 설정된 경우에는 병합하지 않는다. 
 */
// coalesce - 인접한 블록이 free 상태일 경우 병합하고, 리스트 갱신
// coalesce - 인접한 free 블록들을 하나로 병합(coalesce)하여 메모리 단편화를 줄임
static void *coalesce(void *ptr)
{
    // 이전 블록의 할당 여부 확인
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));    

    // 다음 블록의 할당 여부 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));    

    // 현재 블록의 크기 가져오기
    size_t size = GET_SIZE(HDRP(ptr));                      

    // 이전 블록이 재할당 태그가 있는 경우는 병합 금지
    if (GET_TAG(HDRP(PREV_BLKP(ptr))))
        prev_alloc = 1;

    // 양쪽 모두 할당된 경우 → 병합할 필요 없음
    if (prev_alloc && next_alloc) {
        return ptr;
    }

    // 이전 블록은 할당, 다음 블록은 free인 경우 → 다음 블록과 병합
    else if (prev_alloc && !next_alloc) {
        delete_node(ptr);                       // 현재 블록 삭제
        delete_node(NEXT_BLKP(ptr));            // 다음 블록 삭제
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr))); // 총 병합 크기 계산
        PUT(HDRP(ptr), PACK(size, 0));          // 병합된 블록의 헤더 설정
        PUT(FTRP(ptr), PACK(size, 0));          // 병합된 블록의 푸터 설정
    }

    // 이전 블록은 free, 다음 블록은 할당 → 이전 블록과 병합
    else if (!prev_alloc && next_alloc) {
        delete_node(ptr);                         // 현재 블록 삭제
        delete_node(PREV_BLKP(ptr));              // 이전 블록 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));   // 병합된 크기 계산
        PUT(FTRP(ptr), PACK(size, 0));            // 푸터는 현재 위치 기준
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0)); // 헤더는 이전 블록 기준
        ptr = PREV_BLKP(ptr);                     // 포인터를 이전 블록으로 이동
    }

    // 이전과 다음 블록 모두 free → 3개 블록 병합
    else {
        delete_node(ptr);                          // 현재 블록 삭제
        delete_node(PREV_BLKP(ptr));               // 이전 블록 삭제
        delete_node(NEXT_BLKP(ptr));               // 다음 블록 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr))); // 총 병합 크기
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));  // 헤더는 이전 블록 기준
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));  // 푸터는 다음 블록 기준
        ptr = PREV_BLKP(ptr);                      // 포인터는 이전 블록으로 이동
    }

    // 병합된 블록을 가용 리스트에 삽입
    insert_node(ptr, size);
    return ptr; // 병합된 블록의 포인터 반환
}
/*
이 함수는 주변 블록이 가용 상태일 경우 하나로 병합하여 단편화를 줄이고,
병합 전후에는 가용 리스트에서 해당 블록들을 삭제/삽입합니다.
병합 조건은 4가지(병합 없음, 다음만 병합, 이전만 병합, 둘 다 병합)으로 나뉩니다.
*/


/*
 * place - 새로 할당할 블록의 헤더와 푸터를 설정하고,
 *         필요한 경우 블록을 분할하여 남은 공간을 free 블록으로 처리한다.
 */
// place - 주어진 free 블록에 요청된 크기만큼 메모리를 할당하고, 필요한 경우 분할하여 나머지를 free 블록으로 만듬
static void *place(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));        // 현재 블록의 전체 크기
    size_t remainder = ptr_size - asize;          // 남는 공간 (잔여 크기)

    // 리스트에서 해당 블록 제거 (더 이상 가용 상태가 아니므로)
    delete_node(ptr);

    // 남는 공간이 너무 작아서 분할할 수 없는 경우 (오버헤드 고려)
    if (remainder <= DSIZE * 2) {
        PUT(HDRP(ptr), PACK(ptr_size, 1));        // 전체 블록을 할당 상태로 설정 (헤더)
        PUT(FTRP(ptr), PACK(ptr_size, 1));        // 전체 블록을 할당 상태로 설정 (푸터)
    }

    // 요청 크기가 큰 경우 (100 이상) → 앞부분을 free 블록으로 남기고 뒷부분을 할당
    else if (asize >= 100) {
        PUT(HDRP(ptr), PACK(remainder, 0));       // 남은 앞부분을 free 블록으로 설정 (헤더)
        PUT(FTRP(ptr), PACK(remainder, 0));       // 남은 앞부분을 free 블록으로 설정 (푸터)

        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1)); // 뒤쪽 블록을 할당 상태로 설정 (헤더)
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1)); // 뒤쪽 블록을 할당 상태로 설정 (푸터)

        insert_node(ptr, remainder);              // 남은 앞부분 free 블록을 리스트에 삽입
        return NEXT_BLKP(ptr);                    // 할당된 블록의 포인터 반환
    }

    // 일반적인 분할 처리 (앞부분 할당, 뒷부분 free)
    else {
        PUT(HDRP(ptr), PACK(asize, 1));           // 요청 크기만큼 앞부분을 할당 상태로 설정 (헤더)
        PUT(FTRP(ptr), PACK(asize, 1));           // 요청 크기만큼 앞부분을 할당 상태로 설정 (푸터)

        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); // 나머지 블록은 free 상태로 설정 (헤더)
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0)); // 나머지 블록은 free 상태로 설정 (푸터)

        insert_node(NEXT_BLKP(ptr), remainder);   // 나머지 free 블록을 리스트에 삽입
    }

    return ptr; // 할당된 블록의 포인터 반환
}
/*
이 함수는 블록을 할당할 때, 남는 공간이 충분하면 free 블록으로 분할합니다.
asize >= 100인 경우는 반대로 앞부분을 남기고 뒷부분을 할당하는 특별 처리도 합니다.
가용 블록을 사용하는 시점에는 항상 delete_node로 리스트에서 제거한 뒤 처리합니다.
*/

//////////////////////////////////////// End of Helper functions ////////////////////////////////////////


/*
 * mm_init - malloc 패키지를 초기화한다.
 *           힙을 초기화하고, 세분화 리스트들을 NULL로 설정하며,
 *           초기 힙 공간을 확보하여 프롤로그/에필로그를 세팅한다.
 *
 * 반환값: 실패 시 -1, 성공 시 0
 */
// mm_init - 힙 초기화 및 세분화 리스트 초기화
int mm_init(void)
{
    int list;               // 리스트 인덱스
    char *heap_start;       // 힙 시작 포인터

    // 모든 세분화 리스트를 NULL로 초기화
    for (list = 0; list < LISTLIMIT; list++) {
        segregated_free_lists[list] = NULL;
    }

    // 초기 힙 영역 할당 (정렬 패딩 + 프롤로그 + 에필로그 포함)
    if ((long)(heap_start = mem_sbrk(4 * WSIZE)) == -1)
        return -1;

    // 정렬 패딩
    PUT_NOTAG(heap_start, 0);

    // 프롤로그 블록 (2 워드: 헤더 + 푸터)
    PUT_NOTAG(heap_start + (1 * WSIZE), PACK(DSIZE, 1)); // 헤더
    PUT_NOTAG(heap_start + (2 * WSIZE), PACK(DSIZE, 1)); // 푸터

    // 에필로그 블록 (0바이트 할당 블록)
    PUT_NOTAG(heap_start + (3 * WSIZE), PACK(0, 1));

    // 초기 힙 확장 (CHUNKSIZE보다 작음)
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;

    return 0;
}

/*
이 함수는 블록을 할당할 때, 남는 공간이 충분하면 free 블록으로 분할합니다.
asize >= 100인 경우는 반대로 앞부분을 남기고 뒷부분을 할당하는 특별 처리도 합니다.
가용 블록을 사용하는 시점에는 항상 delete_node로 리스트에서 제거한 뒤 처리합니다.
*/

/*
 * mm_malloc - brk 포인터를 증가시켜 블록을 할당합니다.
 *             항상 정렬 크기의 배수인 블록을 할당합니다.
 * 
 *             요청된 크기의 블록을 할당한다.
 *             할당된 블록은 8바이트 정렬을 만족해야 하며,
 *             세분화 리스트에서 적당한 블록을 찾아서 배치한다.
 *
 * Role :
 * 1. mm_malloc 루틴은 할당된 블록 페이로드에 대한 포인터를 반환합니다.
 * 2. 할당된 블록 전체는 힙 영역 내에 있어야 합니다.
 * 3. 할당된 블록 전체는 다른 청크와 겹쳐야 합니다.
 *
 * 반환값: 할당된 블록의 포인터 (8바이트 정렬 보장)
 */
// mm_malloc - 요청된 size만큼 메모리를 할당하는 함수
void *mm_malloc(size_t size)
{
    size_t asize;         // 조정된 블록 크기 (헤더/푸터 포함 및 정렬 고려)
    size_t extendsize;    // 힙을 확장해야 할 경우 필요한 크기
    void *ptr = NULL;     // 최종 할당될 블록 포인터
    int list = 0;         // 세분화 리스트 인덱스

    // 요청한 크기가 0이면 아무것도 하지 않고 NULL 반환
    if (size == 0)
        return NULL;

    // 최소 블록 크기는 16바이트 (헤더+푸터+8바이트 정렬)
    if (size <= DSIZE) {
        asize = 2 * DSIZE;   // 최소 크기로 설정
    } else {
        asize = ALIGN(size + DSIZE); // 요청 크기에 헤더 포함 후 정렬
    }

    // 세분화 리스트에서 적절한 크기의 블록을 탐색
    size_t searchsize = asize;
    while (list < LISTLIMIT) {
        // 마지막 리스트이거나 해당 리스트에 블록이 있는 경우
        if ((list == LISTLIMIT - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            ptr = segregated_free_lists[list]; // 리스트 헤드부터 탐색

            // 재할당 태그가 없고, 크기가 맞는 블록을 찾을 때까지 반복
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))) || (GET_TAG(HDRP(ptr))))) {
                ptr = PRED(ptr); // 이전 블록으로 이동
            }

            // 조건에 맞는 블록을 찾으면 탐색 종료
            if (ptr != NULL)
                break;
        }

        searchsize >>= 1; // 다음 작은 리스트로 이동
        list++;
    }

    // 적절한 블록을 못 찾은 경우 힙 확장
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE); // 최소한 CHUNKSIZE만큼 확장

        // 힙 확장 실패 시 NULL 반환
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }

    // 적절한 위치에 블록을 배치하고, 필요 시 분할
    ptr = place(ptr, asize);

    // 사용자에게 payload 포인터 반환
    return ptr;
}
/*
이 함수는 요청한 크기에 맞게 정렬 및 오버헤드를 고려하여 크기 조정하고,
세분화 리스트에서 적절한 블록을 탐색한 후, 없으면 힙을 확장합니다.
place() 함수를 호출하여 실제로 블록을 할당합니다.
*/


/*
 * mm_free - 지정된 블록을 해제한다.
 *           
 * 규칙 : 해제 후 블록을 병합(coalesce)하고 적절한 리스트에 삽입한다.
 *
 * 반환값: 없음
 */
// mm_free - 주어진 블록을 해제하고, 인접 블록과 병합하여 가용 리스트에 추가
void mm_free(void *ptr)
{
    // 현재 블록의 크기 추출
    size_t size = GET_SIZE(HDRP(ptr));

    // 다음 블록의 재할당 태그 제거 (realloc 최적화용)
    REMOVE_RATAG(HDRP(NEXT_BLKP(ptr)));

    // 현재 블록을 free 상태로 표시 (헤더, 푸터 갱신)
    PUT(HDRP(ptr), PACK(size, 0)); 
    PUT(FTRP(ptr), PACK(size, 0));

    // 가용 리스트에 블록 삽입
    insert_node(ptr, size);

    // 인접 free 블록들과 병합 시도
    coalesce(ptr);

    return;
}

/*
 * mm_realloc - 필요한 경우 힙을 확장하면서 블록을 제자리에 재할당합니다.
 *              새 블록에는 버퍼가 추가되어
 *              다음 재할당이 힙을 확장하지 않고도 수행될 수 있도록 합니다.
 *              단, 블록이 재할당당 일정한 바이트 수만큼 확장된다고 가정합니다.
 *
 *              버퍼가 다음 재할당을 위한 충분한 공간이 없으면
 *              다음 블록에 재할당 태그를 표시합니다. 이 태그로 표시된 빈 블록은
 *              할당이나 병합에 사용할 수 없습니다.
 *              표시된 블록이 재할당에 사용되거나, 힙이 확장되거나,
 *              재할당된 블록이 해제되면 태그가 지워집니다.
 *       
 *            mm_malloc 및 mm_free 측면에서 간단히 구현됨
 *
 * Role : mm_realloc 루틴은 제약 조건이 있는 최소 size 바이트의 할당된 영역에 대한 포인터를 반환합니다.
 *
 */
// mm_realloc - 기존 블록의 크기를 조정하여 재할당하는 함수
void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;         // 새로 반환할 포인터
    size_t new_size = size;      // 요청된 크기
    int remainder;               // 병합 후 남는 여유 공간
    int extendsize;              // 필요한 경우 힙 확장 크기
    int block_buffer;            // 현재 블록에서 확보 가능한 여유 공간

    // 요청 크기가 0이면 NULL 반환
    if (size == 0)
        return NULL;

    // 최소 크기 보장 (16바이트 이상)
    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size + DSIZE); // 헤더 포함 정렬
    }

    // realloc 성능 향상을 위해 버퍼 크기 추가 확보
    new_size += REALLOC_BUFFER;

    // 현재 블록에서 확보 가능한 여유 공간 계산
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;

    // 여유 공간이 부족한 경우 → 재할당 필요
    if (block_buffer < 0) {
        // 다음 블록이 free이거나 에필로그인 경우 병합 시도
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            // 현재 블록 + 다음 블록으로 충분한지 확인
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;

            // 여전히 부족하면 힙 확장
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize; // 확장 후 남는 공간 보정
            }

            // 다음 free 블록은 더 이상 가용 아님
            delete_node(NEXT_BLKP(ptr));

            // 블록 전체 재설정 (병합 + 확장 반영)
            PUT_NOTAG(HDRP(ptr), PACK(new_size + remainder, 1));
            PUT_NOTAG(FTRP(ptr), PACK(new_size + remainder, 1));
        } else {
            // 다음 블록 병합 불가능 → 새 블록 할당 후 복사
            new_ptr = mm_malloc(new_size - DSIZE);  // 새로운 블록 할당
            memcpy(new_ptr, ptr, MIN(size, new_size)); // 내용 복사
            mm_free(ptr); // 기존 블록 해제
        }

        // 최종적으로 확보된 블록에서 여유 공간 재계산
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }

    // 여유 공간이 충분하지 않으면 다음 블록에 재할당 태그 설정
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));

    // 새 블록 포인터 반환
    return new_ptr;
}
/*
이 함수는 기존 블록이 충분히 크면 그대로 사용하고,
다음 블록이 가용한 경우에는 병합하여 확장을 시도합니다.
불가능할 경우 새 블록을 할당하고 데이터를 복사 후 해제합니다.
향후 재할당 가능성을 고려하여 다음 블록에 태그 설정을 수행합니다.
*/
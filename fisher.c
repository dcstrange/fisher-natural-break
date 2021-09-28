#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <error.h>
#include <assert.h>


typedef int u32 ; 
typedef unsigned long value_t;

/*
	fri : sort array
	sec : array num 
	thr : array only num size
	function:
	function:
*/
void sort(void *base, size_t num, size_t size,
	  int (*cmp_func)(const void *, const void *),
	  void (*swap_func)(void *, void *, int size)) ;
int cmpint(const void *a, const void *b) ;
static void u32_swap(void *a, void *b, int size); 
static void generic_swap(void *a, void *b, int size); 


void sort(void *base, size_t num, size_t size,
	  int (*cmp_func)(const void *, const void *),
	  void (*swap_func)(void *, void *, int size))
{
	/* pre-scale counters for performance */
	int i = (num/2 - 1) * size, n = num * size, c, r;

	if (!swap_func)
		swap_func = (size == 4 ? u32_swap : generic_swap);

	/* heapify */
	for ( ; i >= 0; i -= size) {
		for (r = i; r * 2 + size < n; r  = c) {
			c = r * 2 + size;
			if (c < n - size &&
					cmp_func(base + c, base + c + size) < 0)
				c += size;
			if (cmp_func(base + r, base + c) >= 0)
				break;
			swap_func(base + r, base + c, size);
		}
	}

	/* sort */
	for (i = n - size; i > 0; i -= size) {
		swap_func(base, base + i, size);
		for (r = 0; r * 2 + size < i; r = c) {
			c = r * 2 + size;
			if (c < i - size &&
					cmp_func(base + c, base + c + size) < 0)
				c += size;
			if (cmp_func(base + r, base + c) >= 0)
				break;
			swap_func(base + r, base + c, size);
		}
	}
}

static void u32_swap(void *a, void *b, int size)
{
	u32 t = *(u32 *)a;
	*(u32 *)a = *(u32 *)b;
	*(u32 *)b = t;
}

static void generic_swap(void *a, void *b, int size)
{
	char t;

	do {
		t = *(char *)a;
		*(char *)a++ = *(char *)b;
		*(char *)b++ = t;
	} while (--size > 0);
}

struct vcounter 
{
    value_t value;
    unsigned int count;
};


static int cmp_value(const void *a, const void *b)
{
	return *(unsigned int *)a - *(unsigned int *)b;
}


/* ----------------------------------------------------- */ 

void sort_value_get_counter(unsigned int arr[], int arr_size, struct vcounter *sorted_vcounter_arr[], int *vcounter_arr_size)
{
	int i, j;
	unsigned int tmp;
    struct vcounter *vc_arr = calloc(arr_size, sizeof(struct vcounter));
    
	sort(arr, arr_size, sizeof(unsigned int), cmp_value, NULL);

    tmp = arr[0];
	vc_arr[0].value = (value_t)arr[0];
	vc_arr[0].count = 1;

    for(i = 1, j = 0; i < arr_size; i ++){
        if(arr[i] != tmp){
            j++;
            vc_arr[j].value = (value_t)arr[i];
            tmp = arr[i];
        }
        vc_arr[j].count++;
    }

    j++;

    // for(i = 0;i < j; i ++){
    //     printk("[%d,%d]", vc_arr[i].value, vc_arr[i].count);
    // }

    *sorted_vcounter_arr = vc_arr;
    *vcounter_arr_size = j;
}
/* --------------------------------------------------------- */

struct fisher_breaker{
	int m_M, m_K, m_BufSize;
	struct vcounter *sorted_vcounter_arr;

	struct vcounter *m_CumulValues;

	value_t *m_PrevSSM;
    value_t *m_CurrSSM;
	int *m_CB;
	int *m_CBPtr;
	int m_NrCompletedRows;
};

static int init_fisher_breaker(struct fisher_breaker *brk, struct vcounter sorted_vc_arr[], int vc_size, int brk_k)
{
    value_t cwv = 0;
    int cw = 0, w;
    int i;

	brk->sorted_vcounter_arr = sorted_vc_arr;
    brk->m_M = vc_size;
    brk->m_K = brk_k;
    brk->m_BufSize = vc_size - (brk_k -1);
    brk->m_PrevSSM = calloc(brk->m_BufSize, sizeof(value_t));
	brk->m_CBPtr = 0;
	brk->m_NrCompletedRows = 0;

    if(!brk->m_PrevSSM)
        return -1;

    brk->m_CurrSSM = calloc(brk->m_BufSize, sizeof(value_t));
    if(!brk->m_CurrSSM)
        return -1;

    brk->m_CB = calloc(brk->m_BufSize * (brk_k -1) , sizeof(int));
    if(!brk->m_CB)
        return -1;

    brk->m_CumulValues = calloc(vc_size, sizeof(struct vcounter));
	if(!brk->m_CumulValues)
		return -1;

	for(i=0; i < vc_size; i++){
        w = sorted_vc_arr[i].count;
        cw += w;
        cwv += w * sorted_vc_arr[i].value;
        brk->m_CumulValues[i].value = cwv;
        brk->m_CumulValues[i].count = cw;
        if (i < brk->m_BufSize)
				brk->m_PrevSSM[i] = cwv * cwv / cw; // prepare SSM for first class. Last (k-1) values are omitted
    }    
    return 0;
}

static void free_fisher_breaker(struct fisher_breaker *brk)
{
	free(brk->sorted_vcounter_arr);
	free(brk->m_PrevSSM);
	free(brk->m_CurrSSM);
	free(brk->m_CB);
	free(brk->m_CumulValues);
}

static value_t GetW(struct fisher_breaker *brk, int begin, int end)
// Gets sum of weighs for elements b..e.
{
	value_t res;
	assert(begin);    // First element always belongs to class 0, thus queries should never include it.
	assert(begin<=end);
	assert(end<brk->m_M);

	res = brk->m_CumulValues[end].count;
	res -= brk->m_CumulValues[begin-1].count;
	return res;
}

static value_t GetWV(struct fisher_breaker *brk, int begin, int end)
// Gets sum of weighed values for elements b..e
{
	value_t res;
	assert(begin);
	assert(begin<=end);
	assert(end<brk->m_M);

	res = brk->m_CumulValues[end].value;
	res -= brk->m_CumulValues[begin-1].value;
	return res;
}

static value_t GetSSM(struct fisher_breaker *brk, int begin, int end)
// Gets the Squared Mean for elements b..e, multiplied by weight.
// Note that n*mean^2 = sum^2/n when mean := sum/n
{
	value_t res = GetWV(brk, begin,end);
	return res * res / GetW(brk, begin,end);
}

static int FindMaxBreakIndex(struct fisher_breaker *brk, int i, int begin_p, int end_p)
// finds CB[i+m_NrCompletedRows] given that 
// the result is at least bp+(m_NrCompletedRows-1)
// and less than          ep+(m_NrCompletedRows-1)
// Complexity: O(ep-bp) <= O(m)
{
	int m_NrCompletedRows, found_p; 
	value_t minSSM;
	assert(begin_p < end_p);
	assert(begin_p <= i);
	assert(end_p <= i+1);
	assert(i  <  brk->m_BufSize);
	assert(end_p <= brk->m_BufSize);

	m_NrCompletedRows = brk->m_NrCompletedRows;
 int j;
//	for(j =0; j < brk->m_BufSize; j ++)
//	{
//		printf("m_PrevSSM[%d]:%lu, ", j, brk->m_PrevSSM[j]);
//	}

	minSSM = brk->m_PrevSSM[begin_p] + GetSSM(brk, begin_p+m_NrCompletedRows, i+m_NrCompletedRows);
	found_p = begin_p;

	while (++begin_p < end_p)
	{
		value_t currSSM =  brk->m_PrevSSM[begin_p] + GetSSM(brk, begin_p+m_NrCompletedRows, i+m_NrCompletedRows);
		if (currSSM > minSSM)
		{
			minSSM = currSSM;
			found_p = begin_p;
		}
		//printf("currSSM[%d]: %lu, ", begin_p, currSSM);

	}
	brk->m_CurrSSM[i] = minSSM;
//	printf("\nfound_p: %d\n", found_p);

	return found_p;
}


static void CalcRange(struct fisher_breaker *brk, int bi, int ei, int bp, int ep)
// find CB[i+m_NrCompletedRows]
// for all i>=bi and i<ei given that
// the results are at least bp+(m_NrCompletedRows-1)
// and less than            ep+(m_NrCompletedRows-1)
// Complexity: O(log(ei-bi)*Max((ei-bi),(ep-bp))) <= O(m*log(m))
{
	int mi, mp;
	assert(bi <= ei);

	assert(ep <= ei);
	assert(bp <= bi);

	if (bi == ei)
		return;
	assert(bp < ep);

	mi = (bi + ei)/2;
	mp = FindMaxBreakIndex(brk, mi, bp, ep < mi+1 ? ep : mi+1);

	assert(bp <= mp);
	assert(mp <  ep);
	assert(mp <= mi);
	
	// solve first half of the sub-problems with lower 'half' of possible outcomes
	CalcRange(brk, bi, mi, bp, mi < mp+1 ? mi : mp+1); 

	brk->m_CBPtr[mi] = mp; // store result for the middle element.

	// solve second half of the sub-problems with upper 'half' of possible outcomes
	CalcRange(brk, mi+1, ei, mp, ep);
}


static void CalcAll(struct fisher_breaker *brk)
// complexity: O(m*log(m)*k)
{
	int m_BufSize = brk->m_BufSize;
	if (brk->m_K >= 2) {
		brk->m_CBPtr = brk->m_CB;
		for (brk->m_NrCompletedRows=1; brk->m_NrCompletedRows < brk->m_K-1; brk->m_NrCompletedRows++)
		{
			value_t *swap;
			CalcRange(brk, 0, m_BufSize, 0, m_BufSize); // complexity: O(m*log(m))

			swap = brk->m_PrevSSM;
			brk->m_PrevSSM = brk->m_CurrSSM;
			brk->m_CurrSSM = swap;

			brk->m_CBPtr += m_BufSize;
		}
	}
}

static void get_fisher_brk(struct fisher_breaker* brk, value_t *brk_arr[])
{
	value_t *breaks_arr;
	assert(brk->m_K);

	breaks_arr = calloc(brk->m_K, sizeof(value_t));
	if(!breaks_arr)
		return;

	if (brk->m_K > 1)
	{
		int lastClassBreakIndex, k;
		CalcAll(brk);

		lastClassBreakIndex = FindMaxBreakIndex(brk, brk->m_BufSize-1, 0, brk->m_BufSize);

		k = brk->m_K;
		while (--k)
		{
			breaks_arr[k] = brk->sorted_vcounter_arr[lastClassBreakIndex+k].value;
			assert(lastClassBreakIndex < brk->m_BufSize);
			if (k > 1)
			{
				brk->m_CBPtr -= brk->m_BufSize;
				lastClassBreakIndex = brk->m_CBPtr[lastClassBreakIndex];
			}
		}
		assert(brk->m_CBPtr == brk->m_CB);
	}
	breaks_arr[0] = brk->sorted_vcounter_arr[0].value; // break for the first class is the minimum of the dataset.
	*brk_arr = breaks_arr;
}

int fisher_natural_breaks(unsigned int values[], int values_cnt, int brk_n, unsigned int brks[])
{
	struct vcounter *sorted_vconter; 
    int vconter_size;
    struct fisher_breaker brk;
	int i, err;
	value_t *brk_arr;

    sort_value_get_counter(values, values_cnt, &sorted_vconter, &vconter_size);

    err = init_fisher_breaker(&brk, sorted_vconter, vconter_size, brk_n);
    if(err)
		return err;
    
	get_fisher_brk(&brk, &brk_arr);
	if(!brk_arr)
		return -1;

    for(i = 0; i<brk_n; i++)
		brks[i] = (unsigned int)brk_arr[i];
        
	free_fisher_breaker(&brk);
	free(brk_arr);
	return 0;
}




int main()
{

    value_t arr[27] = {8,3,2,1,9,2,9,8,2,1,3,1,2,4,2,2,1,8,8,8,9,8,9,23,21,31,25};

    int sorted_vconter_size = -1;
    int i=0;
    int err;

	unsigned int brks[3];
	fisher_natural_breaks(arr, 16180, 3, brks);

	for(i = 0; i < 3; i++)
	{
		printf("%d,", brks[i]);
	}
	printf("\n");
    //value_t arr[10000];
    // for(;i< 10000; i++){
    //     arr[i] = rand() % 1000;
    // }

    return 0;
}



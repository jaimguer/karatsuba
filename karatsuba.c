#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <gmp.h>
#include <time.h>
#include "scaffold32.h"
#include <stdint.h>

#define SIZE sizeof(uint32_t)
#define BASE 4294967296
#define MAX(a,b) ((a) < (b) ? (b) : (a))
#define MIN(a,b) ((a) < (b) ? (a) : (b))
#define __nothrow __attribute__((nothrow))
#define __flatten __attribute__((flatten))

void __flatten
     __nothrow
     sum(uint32_t* a,
         uint32_t* b,
         uint32_t* c,
         uint32_t wa,
         uint32_t wb)
{
    uint32_t* longerNumber  = wa < wb ? b : a;
    uint32_t* shorterNumber = wa < wb ? a : b;
    uint32_t carry = 0;

    uint32_t i;
    for(i = 0; i < MIN(wa, wb); i++)
    {
        uint64_t s = ((uint64_t)longerNumber[i])  +
                     ((uint64_t)shorterNumber[i]) +
                     carry;
        c[i]       = s % (uint64_t)BASE;
        carry      = s / (uint64_t)BASE;
    }

    for(i = MIN(wa, wb); i < MAX(wa, wb); i++)
    {
        uint64_t s = (uint64_t)longerNumber[i] + carry;
        c[i]       = s % (uint64_t)BASE;
        carry      = s / (uint64_t)BASE;
    }

    c[i] = carry;
}

void __flatten
     __nothrow
     sub(uint32_t* a,
         uint32_t* b,
         uint32_t* c,
         uint32_t wa,
         uint32_t wb)
{
    uint32_t borrow = 0;
    uint_fast32_t i;

    for (i = 0; i < wb; i++)
    {
        uint64_t temp = ((uint64_t)b[i] + borrow) % (uint64_t)BASE;
        borrow        = (uint64_t)temp > (uint64_t)a[i];
        c[i]          = (uint64_t)(a[i] + (uint64_t)BASE) - temp;
    }

    for(i = wb; i < wa; i++)
    {
        c[i]   = ((uint64_t)a[i] - (uint64_t)borrow) % (uint64_t)BASE;
        borrow = borrow > a[i];
    }
}

void __flatten
     __nothrow
     naive(uint32_t* a,
           uint32_t* b,
           uint32_t* c,
           uint32_t wa,
           uint32_t wb)
{
    memset(c, 0, MAX(wa, wb) * SIZE);

    uint_fast32_t i;

    for(i = 0; i < wa; i++)
    {
        uint32_t carry = 0;
        uint_fast32_t j;
        for (j = 0; j < wb; j++)
        {
            uint64_t p = ((uint64_t)a[i]  *
                          (uint64_t)b[j]) +
                         c[i + j] +
                         carry;
            c[i + j]   = p % (uint64_t)BASE;
            carry      = p / (uint64_t)BASE;
        }
        c[i + wb] = carry;
    }
}

void __flatten
     __nothrow
     karatsuba(uint32_t* a,
               uint32_t* b,
               uint32_t* c,
               uint32_t wa,
               uint32_t wb)
{
    if (wa <= 26 || wb <= 26) { naive(a, b, c, wa, wb); }
    else
    { /***************** Value Calculations *****************/
        uint32_t n           = (1 + MAX(wa, wb)) / 2;
        uint32_t low1        = MIN(wa, n);
        uint32_t low2        = MIN(wb, n);
        uint32_t high1       = wa - low1;
        uint32_t high2       = wb - low2;
        uint32_t t1Wc        = MAX(high1, low1) + 1;
        uint32_t t2Wc        = MAX(high2, low2) + 1;
        uint32_t w3Wc        = t1Wc  + t2Wc;
        uint32_t w2Wc        = high1 + high2;
        uint32_t w4Wc        = low1  + low2;
        uint32_t totalDiffWc = w3Wc;
        uint32_t carryWc     = n > w4Wc ? 0 : w4Wc - n;
        uint32_t w3HatWc     = MAX(totalDiffWc, carryWc) + 1;
        uint_fast32_t i;
        uint_fast32_t j;

        /**** Memory Allocation ****/
        uint32_t* pad = malloc((t1Wc + t2Wc + w3Wc + w2Wc + w4Wc +
                                w3Wc + totalDiffWc + w3HatWc + w2Wc +
                                carryWc) * SIZE);

        /**** Assignment of pointers ****/
        uint32_t* u1        = a + low1;
        uint32_t* u2        = a;
        uint32_t* v1        = b + low2;
        uint32_t* v2        = b;
        uint32_t* t1        = pad;
        uint32_t* t2        = pad + t1Wc;
        uint32_t* w3        = pad + t1Wc + t2Wc;
        uint32_t* w2        = pad + t1Wc + t2Wc + w3Wc;
        uint32_t* w4        = pad + t1Wc + t2Wc + w3Wc + w2Wc;
        uint32_t* tempDiff  = pad + t1Wc + t2Wc + w3Wc + w2Wc + w4Wc;
        uint32_t* totalDiff = pad + t1Wc + t2Wc + w3Wc + w2Wc + w4Wc + w3Wc;
        uint32_t* w3Hat     = pad + t1Wc + t2Wc + w3Wc + w2Wc + w4Wc + w3Wc + totalDiffWc;
        uint32_t* w2Hat     = pad + t1Wc + t2Wc + w3Wc + w2Wc + w4Wc + w3Wc + totalDiffWc + w3HatWc;
        uint32_t* carry     = w4 + n;

        /***************** Sums *****************/
        sum(u1, u2, t1, high1, low1);
        sum(v1, v2, t2, high2, low2);

        /*********** Recursive Calls ************/
        karatsuba(t1, t2, w3, t1Wc,  t2Wc);
        karatsuba(u1, v1, w2, high1, high2);
        karatsuba(u2, v2, w4, low1,  low2);

        /************* Subtraction **************/
        sub(w3, w2, tempDiff, w3Wc, w2Wc);
        sub(tempDiff, w4, totalDiff, w3Wc, w4Wc);

        /************ Final Computation ***************/
        sum(totalDiff, carry, w3Hat, totalDiffWc, carryWc);

        carry = w3Hat + n;
        carryWc = n > w3HatWc ? 0 : w3HatWc - n;

        sum(w2, carry, w2Hat, MAX(w2Wc, carryWc) + 1, carryWc);

        /****** Generate answer *****/
        for(i = 0; i < n; i++)         { c[i] = w4[i]; }
        for(j = 0; i < (2 * n); j++)   { c[i] = w3Hat[j]; i++; }
        for(j = 0; i < (wa + wb); j++) { c[i] = w2Hat[j]; i++; }
    }
}

void Product32(void *a,
               void *b,
               void *c,
               unsigned int wa,
               unsigned int ba,
               unsigned int wb,
               unsigned int bb,
               unsigned int *wc,
               unsigned int *bc)
{
    karatsuba((uint32_t*)a, (uint32_t*)b, (uint32_t*)c, (uint32_t)wa, (uint32_t)wb);
    *wc = wa + wb;
}

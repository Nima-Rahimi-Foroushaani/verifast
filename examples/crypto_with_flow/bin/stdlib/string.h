#ifndef STRING_H
#define STRING_H

#include <stddef.h>
//@ #include <crypto.gh>

char *strcpy(char *d, char *s);
    //@ requires [?f]string(s, ?cs) &*& chars(d, length(cs) + 1, _);
    //@ ensures [f]string(s, cs) &*& chars(d, length(cs) + 1, append(cs, {0})) &*& result == d;

void memcpy(void *array, void *array0, size_t count);
    /*@ requires chars(array, count, ?cs) &*&
                 [?f]crypto_chars(?kind, array0, count, ?cs0) &*&
                 //minimum size prevents comparing sequence of same byte (see memcmp)
                 //otherwise guessing would become easier complexity wise
                 kind == normal || count >= MINIMAL_STRING_SIZE; @*/
    /*@ ensures  crypto_chars(kind, array, count, cs0) &*&
                 [f]crypto_chars(kind, array0, count, cs0); @*/

void memmove(void *dest, void *src, size_t count);
    /*@
    requires
        chars(src, count, ?cs) &*&
        dest <= src ?
            chars(dest, src - dest, _)
        :
            chars(src + count, dest - src, _);
    @*/
    /*@
    ensures
        chars(dest, count, cs) &*&
        dest <= src ?
            chars(dest + count, src - dest, _)
        :
            chars(src, dest - src, _);
    @*/

int strlen(char *string);
    //@ requires [?f]string(string, ?cs);
    //@ ensures [f]string(string, cs) &*& result == length(cs);

int memcmp(char *array, char *array0, size_t count);
    /*@ requires principal(?principal, ?values_count) &*&
                 [?f1]crypto_chars(?kind1, array, ?n1, ?cs) &*&
                 [?f2]crypto_chars(?kind2, array0, ?n2, ?cs0) &*& 
                 count <= n1 &*& count <= n2 &*& 
                 kind1 == normal && kind2 == normal ?
                   true : count >= MINIMAL_STRING_SIZE; @*/
    /*@ ensures  [f1]crypto_chars(?kind1_, array, n1, cs) &*&
                 [f2]crypto_chars(?kind2_, array0, n2, cs0) &*&
                 true == ((result == 0) == (take(count, cs) == take(count, cs0))) &*&
                 (
                   //if guessing a secret value failed, network permissions are revoked
                   // *otherwise one could keep guessing untill success
                   // *MINIMAL_STRING_SIZE ensures correct guess is unlikely
                   result != 0 && (kind1 == secret || kind2 == secret) ?
                       true : principal(principal, values_count)
                 ) &*&
                 result != 0 ? 
                   //if comparison failed kinds remain
                   kind1_ == kind1 && kind2_ == kind2
                 : 
                   //if comparison succeeded kinds become the same
                   kind1_ == kind2_ &*&
                   //the resulting kind follows the rules of memcmp_kinds
                   kind1_ == memcmp_kinds(kind1, n1, kind2, n2) &*&
                   //comparing a garbage value successfully to a non-garbage value results in a collision
                   kind1 == kind2 || (kind1 != garbage && kind2 != garbage) || col; @*/

int strcmp(char *s1, char *s2);
    //@ requires [?f1]string(s1, ?cs1) &*& [?f2]string(s2, ?cs2);
    //@ ensures [f1]string(s1, cs1) &*& [f2]string(s2, cs2) &*& true == ((result == 0) == (cs1 == cs2));

char *memchr(char *array, char c, size_t count);
    //@ requires [?f]chars(array, count, ?cs);
    //@ ensures [f]chars(array, count, cs) &*& result == 0 ? mem(c, cs) == false : mem(c, cs) == true &*& result == array + index_of(c, cs);

char* strchr(char *str, char c);
    //@ requires [?f]string(str, ?cs);
    /*@ ensures
            [f]string(str, cs) &*&
            c == 0 ? 
                result == str + length(cs)
            : 
                result == 0 ?
                    mem(c, cs) == false
                :
                    mem(c, cs) == true &*& result == str + index_of(c, cs);
    @*/

void* memset(void *array, char value, size_t size);
    //@ requires chars(array, size, ?cs);
    //@ ensures chars(array, size, ?cs1) &*& all_eq(cs1, value) == true &*& result == array;

char *strdup(char *string);
    //@ requires [?f]string(string, ?cs);
    //@ ensures [f]string(string, cs) &*& result == 0 ? true : string(result, cs) &*& malloc_block_chars(result, length(cs) + 1);

#endif

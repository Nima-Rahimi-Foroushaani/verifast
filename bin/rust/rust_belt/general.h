#ifndef GENERAL_GH
#define GENERAL_GH

#include "stdint.h"
//@ #include "lifetime_logic.gh"
/*@

predicate atomic_context();
predicate atomic_mask(mask_t mask);
predicate atomic_space(mask_t mask, predicate() inv;);
/* This would be the existentially quantified `R` in the derived rule on Ralf Jung's thesis in the middle of page 67.
See https://research.ralfj.de/phd/thesis-screen.pdf */
predicate close_atomic_space_token(mask_t spaceMask, predicate() inv);

lemma void create_atomic_space(mask_t mask, predicate() inv);
    requires !mask_is_empty(mask) &*& inv();
    ensures atomic_space(mask, inv);

/* This lemma is a mask changing view-shift that opens atomic_space(spaceMask, inv). Hence, It can just be used in the context
of proving a Hoare triple for an atomic `e` (See Iris HOARE-VS-ATOMIC). We need to have `atomic_context()` as an evidence for that. */
lemma void open_atomic_space(mask_t spaceMask, predicate() inv);
    requires atomic_context() &*& [?f]atomic_space(spaceMask, inv) &*& atomic_mask(?currentMask) &*& mask_le(spaceMask, currentMask) == true;
    ensures atomic_context() &*& [f]atomic_space(spaceMask, inv) &*& atomic_mask(mask_diff(currentMask, spaceMask))
            &*& close_atomic_space_token(spaceMask, inv) &*& inv();

lemma void close_atomic_space(mask_t spaceMask);
    requires atomic_context() &*& atomic_mask(?currentMask) &*& close_atomic_space_token(spaceMask, ?inv) &*& inv();
    ensures atomic_context() &*& atomic_mask(mask_union(currentMask, spaceMask));

predicate_ctor simple_share(fixpoint(thread_id_t, void *, predicate(;)) frac_borrow_content)(lifetime_t k, thread_id_t t, void *l) =
    frac_borrow(k, frac_borrow_content(t, l));
predicate_ctor shared_ref_own(predicate(lifetime_t, thread_id_t, void *) pointee_shr, lifetime_t k)(thread_id_t t, void *l) = [_]pointee_shr(k, t, l);

predicate bool_own(thread_id_t t, bool v;) = true;
predicate char_own(thread_id_t t, uint32_t v;) = 0 <= v && v <= 0xD7FF || 0xE000 <= v && v <= 0x10FFFF;
predicate raw_ptr_own(thread_id_t t, void *v;) = true;

predicate i8_own(thread_id_t t, int8_t v;) = true;
predicate i16_own(thread_id_t t, int16_t v;) = true;
predicate i32_own(thread_id_t t, int32_t v;) = true;
predicate i64_own(thread_id_t t, int64_t v;) = true;
predicate i128_own(thread_id_t t, int128_t v;) = true;
predicate isize_own(thread_id_t t, intptr_t v;) = true;

predicate u8_own(thread_id_t t, uint8_t v;) = true;
predicate u16_own(thread_id_t t, uint16_t v;) = true;
predicate u32_own(thread_id_t t, uint32_t v;) = true;
predicate u64_own(thread_id_t t, uint64_t v;) = true;
predicate u128_own(thread_id_t t, uint128_t v;) = true;
predicate usize_own(thread_id_t t, uintptr_t v;) = true;

predicate_ctor bool_full_borrow_content(thread_id_t t, bool *l)(;) = *l |-> ?_;
predicate_ctor char_full_borrow_content(thread_id_t t, uint32_t *l)(;) = *l |-> ?c &*& char_own(t, c);
predicate_ctor raw_ptr_full_borrow_content(thread_id_t t, void **l)(;) = *l |-> ?_;

predicate_ctor i8_full_borrow_content(thread_id_t t, int8_t *l)(;) = *l |-> ?_;
predicate_ctor i16_full_borrow_content(thread_id_t t, int16_t *l)(;) = *l |-> ?_;
predicate_ctor i32_full_borrow_content(thread_id_t t, int32_t *l)(;) = *l |-> ?_;
predicate_ctor i64_full_borrow_content(thread_id_t t, int64_t *l)(;) = *l |-> ?_;
predicate_ctor i128_full_borrow_content(thread_id_t t, int128_t *l)(;) = *l |-> ?_;
predicate_ctor isize_full_borrow_content(thread_id_t t, intptr_t *l)(;) = *l |-> ?_;

predicate_ctor u8_full_borrow_content(thread_id_t t, uint8_t *l)(;) = *l |-> ?_;
predicate_ctor u16_full_borrow_content(thread_id_t t, uint16_t *l)(;) = *l |-> ?_;
predicate_ctor u32_full_borrow_content(thread_id_t t, uint32_t *l)(;) = *l |-> ?_;
predicate_ctor u64_full_borrow_content(thread_id_t t, uint64_t *l)(;) = *l |-> ?_;
predicate_ctor u128_full_borrow_content(thread_id_t t, uint128_t *l)(;) = *l |-> ?_;
predicate_ctor usize_full_borrow_content(thread_id_t t, uintptr_t *l)(;) = *l |-> ?_;

predicate type_interp<T>(; predicate(thread_id_t, T) T_own, fixpoint(thread_id_t, void *, predicate()) T_full_borrow_content, predicate(lifetime_t, thread_id_t, void *) T_share);

lemma void share_full_borrow<T>(lifetime_t k, thread_id_t t, void *l);
    requires type_interp<T>(?T_own, ?T_full_borrow_content, ?T_share) &*& full_borrow(k, T_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ensures type_interp<T>(T_own, T_full_borrow_content, T_share) &*& [_]T_share(k, t, l) &*& [q]lifetime_token(k);
@*/

#endif

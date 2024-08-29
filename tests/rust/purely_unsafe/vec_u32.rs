/**
 * This is a naive version of an unsafe vector for presentation purposes
 */
use std::{alloc::Layout, process::abort};

struct VecU32 {
    buf: *mut u32,
    len: usize,
}

/*@
//fix len(v: VecU32) -> usize { v.len }
pred VecU32(ptr: *VecU32; len: usize) = (*ptr).buf |-> ?buf &*& (*ptr).len |-> len &*& if std::ptr::is_null(buf) { len == 0 } else {
    len > 0 &*& len <= 0xFFFF &*& buf[..len] |-> ?vs &*&
    std::alloc::alloc_block(buf as *u8, std::alloc::Layout::from_size_align_(len * std::mem::size_of_::<u32>(), std::mem::align_of_::<u32>()))
};
@*/

impl VecU32 {
    pub unsafe fn new() -> VecU32
//@ req true;
    //@ ens result.len == 0;
    {
        Self {
            buf: std::ptr::null_mut(),
            len: 0,
        }
    }

    pub unsafe fn len(this: *const VecU32) -> usize
//@ req [?f](*this).len |-> ?len;
    //@ ens [f](*this).len |-> len &*& result == len;
    {
        (*this).len
    }

    pub unsafe fn push_back(this: *mut VecU32, v: u32)
    //@ req thread_token(?t) &*& VecU32(this, ?length);
    //@ ens thread_token(t) &*& VecU32(this, length + 1);
    {
        let Self { len, buf } = *this;
        if len == 0xFFFF { //TODO: Fix truncating cast to target dep size
            abort()
        };
        let n = len + 1;
        let l = Layout::array::<u32>(n).unwrap();
        let p = std::alloc::alloc(l) as *mut u32;
        if p.is_null() {
            std::alloc::handle_alloc_error(l)
        }
        //@ u8s__to_array_(p, n);
        if !buf.is_null() {
            //@ array__split(p, len);
            std::intrinsics::copy_nonoverlapping(buf, p, len);
            let lo = Layout::array::<u32>(len).unwrap();
            //@ leak <std::alloc::Layout>.own(t, lo);
            //@ array_to_array_(buf);
            //@ array__to_u8s_(buf, len);
            std::alloc::dealloc(buf as *mut u8, lo);
        }
        std::ptr::write(p.add(len), v);
        (*this).buf = p;
        (*this).len = n;
        //@ open array_(p + n, 0, _);
        //@ leak <std::alloc::Layout>.own(t, l);
        //@ close array(p + len, 1, [ v ]);
        //@ if buf != 0 { array_join(p); }
    }
}

use super::*;

#[test]
fn test_return_value() {
    let code = "
        unsafe fn f() -> i32 { g() }
        unsafe fn g() -> i32 { 0 }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0]);
}

#[test]
fn test_ptr() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x = 0;
            g(&mut x);
            x
        }
        unsafe fn g(p: *mut i32) {
            *p = 1;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_ptr2() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x = 0;
            let mut y = 0;
            g(0, &mut x, 0, &mut y);
            x + y
        }
        unsafe fn g(n: i32, p: *mut i32, m: i32, q: *mut i32) {
            *p = 1;
            *q = 2;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![3]);
}

#[test]
fn test_ptr_weak() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x = 0;
            let mut y = 0;
            let p: *mut i32 = if b { &mut x } else { &mut y };
            g(p);
            x
        }
        unsafe fn g(p: *mut i32) {
            *p = 1;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

#[test]
fn test_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f() -> i32 {
            let mut x = S { x: 0, y: 0 };
            g(&mut x);
            x.x + x.y
        }
        unsafe fn g(p: *mut S) {
            (*p).x = 1;
            (*p).y = 2;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![3]);
}

#[test]
fn test_struct_ptr() {
    let code = "
        struct S { x: *mut i32, y: *mut i32 }
        unsafe fn f() -> i32 {
            let mut x = 0;
            let mut y = 0;
            let s = S { x: &mut x, y: &mut y };
            g(s);
            x + y
        }
        unsafe fn g(s: S) {
            *s.x = 1;
            *s.y = 2;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![3]);
}

#[test]
fn test_struct_ptr2() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: *mut i32, y: *mut i32 }
        unsafe fn f() -> i32 {
            let mut x = 0;
            let mut y = 0;
            let mut z = 0;
            let mut w = 0;
            let t1 = T { x: &mut x, y: &mut y };
            let t2 = T { x: &mut z, y: &mut w };
            let s = S { x: t1, y: t2 };
            g(s);
            x + y + z + w
        }
        unsafe fn g(s: S) {
            *s.x.x = 1;
            *s.x.y = 2;
            *s.y.x = 3;
            *s.y.y = 4;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![10]);
}

#[test]
fn test_array() {
    let code = "
        unsafe fn f() -> i32 {
            let mut arr = [0, 0];
            g(&mut arr);
            arr[0] + arr[1]
        }
        unsafe fn g(p: *mut [i32; 2]) {
            (*p)[0] = 1;
            (*p)[1] = 2;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![3]);
}

#[test]
fn test_array_ptr() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x = 0;
            let mut y = 0;
            let arr = [&mut x as *mut i32, &mut y as *mut i32];
            g(arr);
            x + y
        }
        unsafe fn g(s: [*mut i32; 2]) {
            *s[0] = 1;
            *s[1] = 2;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![3]);
}

#[test]
fn test_array_ptr2() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x = 0;
            let mut y = 0;
            let mut z = 0;
            let mut w = 0;
            let arr1 = [&mut x as *mut i32, &mut y as *mut i32];
            let arr2 = [&mut z as *mut i32, &mut w as *mut i32];
            let arr = [arr1, arr2];
            g(arr);
            x + y + z + w
        }
        unsafe fn g(arr: [[*mut i32; 2]; 2]) {
            *arr[0][0] = 1;
            *arr[0][1] = 2;
            *arr[1][0] = 3;
            *arr[1][1] = 4;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![10]);
}

#[test]
fn test_write_local() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x = 0;
            g(b, &mut x);
            x
        }
        unsafe fn g(b: bool, p: *mut i32) {
            if b {
                *p = 0;
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_write() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) -> i32 {
            g(b, p);
            *p
        }
        unsafe fn g(b: bool, p: *mut i32) {
            if b {
                *p = 0;
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![2]);

    assert_eq!(as_int(ret(&result[1])), vec![0]);
    assert_eq!(result[1].writes.len(), 1);
    assert_eq!(result[1].writes.as_vec()[0].0, vec![2]);
    assert_eq!(result[1].reads.len(), 0);
}

#[test]
fn test_write2() {
    let code = "
        unsafe fn f(p: *mut i32, q: *mut i32, b: bool) -> i32 {
            g(p, q, b);
            *p
        }
        unsafe fn g(p: *mut i32, q: *mut i32, b: bool) {
            if b {
                *p = 0;
            } else {
                *q = 0;
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![1]);
    assert_eq!(result[0].reads.len(), 0);

    assert!(ret(&result[1]).intv.is_top());
    assert_eq!(result[1].writes.len(), 1);
    assert_eq!(result[1].writes.as_vec()[0].0, vec![2]);
    assert_eq!(result[1].reads.len(), 1);
    assert_eq!(result[1].reads.as_vec()[0].0, vec![1]);
}

#[test]
fn test_write_weak() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32, q: *mut i32) -> i32 {
            let r = if b { p } else { q };
            g(b, r);
            *p
        }
        unsafe fn g(b: bool, p: *mut i32) {
            if b {
                *p = 0;
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![2]);
}

#[test]
fn test_read_local() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x = 0;
            g(b, &mut x)
        }
        unsafe fn g(b: bool, p: *mut i32) -> i32 {
            let mut x = 0;
            if b {
                x = *p;
            }
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_read() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) -> i32 {
            g(b, p)
        }
        unsafe fn g(b: bool, p: *mut i32) -> i32 {
            let mut x = 0;
            if b {
                x = *p;
            }
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 0);

    assert!(ret(&result[1]).intv.is_top());
    assert_eq!(result[1].writes.len(), 0);
    assert_eq!(result[1].reads.len(), 1);
    assert_eq!(result[1].reads.as_vec()[0].0, vec![2]);
}

#[test]
fn test_read2() {
    let code = "
        unsafe fn f(p: *mut i32, q: *mut i32, b: bool) -> i32 {
            g(p, q, b)
        }
        unsafe fn g(p: *mut i32, q: *mut i32, b: bool) -> i32 {
            let mut x = 0;
            if b {
                x = *p;
            } else {
                x = *q;
            }
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![1]);

    assert!(ret(&result[1]).intv.is_top());
    assert_eq!(result[1].writes.len(), 0);
    assert_eq!(result[1].reads.len(), 1);
    assert_eq!(result[1].reads.as_vec()[0].0, vec![2]);
}

#[test]
fn test_read_weak() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32, q: *mut i32) -> i32 {
            let r = if b { p } else { q };
            g(b, r)
        }
        unsafe fn g(b: bool, p: *mut i32) -> i32 {
            let mut x = 0;
            if b {
                x = *p;
            }
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 0);

    assert!(ret(&result[1]).intv.is_top());
    assert_eq!(result[1].writes.len(), 0);
    assert_eq!(result[1].reads.len(), 2);
    assert_eq!(result[1].reads.as_vec()[0].0, vec![2]);
    assert_eq!(result[1].reads.as_vec()[1].0, vec![3]);
}

#[test]
fn test_write_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            g(b, &mut (*p).x);
            (*p).x
        }
        unsafe fn g(b: bool, p: *mut i32) {
            if b {
                *p = 0;
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![2, 0]);

    assert_eq!(as_int(ret(&result[1])), vec![0]);
    assert_eq!(result[1].writes.len(), 1);
    assert_eq!(result[1].writes.as_vec()[0].0, vec![2, 0]);
    assert_eq!(result[1].reads.len(), 0);
}

#[test]
fn test_write_array() {
    let code = "
        unsafe fn f(b: bool, p: *mut [i32; 2]) -> i32 {
            g(b, &mut (*p)[0]);
            (*p)[0]
        }
        unsafe fn g(b: bool, p: *mut i32) {
            if b {
                *p = 0;
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![2]);
}

#[test]
fn test_double() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x = 0;
            let mut p: *mut i32 = &mut x;
            g(&mut p);
            x
        }
        unsafe fn g(p: *mut *mut i32) {
            **p = 1;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_double_ptr() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x = 0;
            let mut p: *mut i32 = &mut x;
            g(&mut p);
            *p
        }
        unsafe fn g(p: *mut *mut i32) {
            **p = 1;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_double_swap() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x1 = 0;
            let mut p1: *mut i32 = &mut x1;
            let q1: *mut *mut i32 = &mut p1;
            let mut x2 = 0;
            let mut p2: *mut i32 = &mut x2;
            let q2: *mut *mut i32 = &mut p2;
            g(q1, q2);
            x1 = 2;
            x2 = 1;
            *p2 - *p1
        }
        unsafe fn g(p: *mut *mut i32, q: *mut *mut i32) {
            let a = *p;
            let b = *q;
            *p = b;
            *q = a;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_double_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f() -> i32 {
            let mut x = S { x: 0, y: 0 };
            let mut y = 0;
            let mut p: *mut i32 = &mut y;
            g(&mut x, &mut p);
            x.x = 1;
            *p
        }
        unsafe fn g(p: *mut S, q: *mut *mut i32) {
            *q = &mut (*p).x;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_double_weak() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut x1 = 0;
            let mut p1: *mut i32 = &mut x1;
            let mut q1: *mut *mut i32 = &mut p1;
            let mut x2 = 0;
            let mut p2: *mut i32 = &mut x2;
            let mut q2: *mut *mut i32 = &mut p2;
            g(b, q1, q2);
            x1 = 1;
            x2 = 2;
            *p1
        }
        unsafe fn g(b: bool, p: *mut *mut i32, q: *mut *mut i32) {
            let r = *p;
            let s = *q;
            *p = if b { r } else { s };
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1, 2]);
}

#[test]
fn test_double_dangling() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x1 = 0;
            let mut p1: *mut i32 = &mut x1;
            let mut q1: *mut *mut i32 = &mut p1;
            g(q1);
            *p1
        }
        unsafe fn g(p: *mut *mut i32) {
            let mut x = 0;
            *p = &mut x;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert!(ret(&result[0]).is_bot());
}

#[test]
fn test_ptr_return() {
    let code = "
        unsafe fn f() -> i32 {
            let mut x = 0;
            let p: *mut i32 = &mut x;
            let q = g(p);
            x = 1;
            *q
        }
        unsafe fn g(p: *mut i32) -> *mut i32 {
            p
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_malloc() {
    let code = "
        extern crate libc;
        extern \"C\" {
            fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
        }
        unsafe fn f() -> i32 {
            let mut x = 0;
            let mut p: *mut i32 = &mut x;
            g(&mut p);
            *p = 1;
            *p
        }
        unsafe fn g(p: *mut *mut i32) {
            *p = malloc(4) as *mut i32;
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_malloc_return() {
    let code = "
        extern crate libc;
        extern \"C\" {
            fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
        }
        unsafe fn f() -> i32 {
            let q = g();
            *q = 1;
            *q
        }
        unsafe fn g() -> *mut i32 {
            malloc(4) as *mut i32
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

#[test]
fn test_while_malloc() {
    let code = "
        extern crate libc;
        extern \"C\" {
            fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
        }
        unsafe fn f() {
            let mut i = 0;
            let mut p: *mut i32 = &mut i;
            while i < 10 {
                i += 1;
                p = g();
            }
        }
        unsafe fn g() -> *mut i32 {
            malloc(4) as *mut i32
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].heap.len(), 1);
}

#[test]
fn test_malloc_malloc() {
    let code = "
        extern crate libc;
        extern \"C\" {
            fn malloc(_: libc::c_ulong) -> *mut libc::c_void;
        }
        unsafe fn f() -> i32 {
            let p = g();
            **p
        }
        unsafe fn g() -> *mut *mut i32 {
            let p = malloc(4) as *mut i32;
            *p = 1;
            let q = malloc(4) as *mut *mut i32;
            *q = p;
            q
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![1]);
}

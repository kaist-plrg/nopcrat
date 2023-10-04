use super::*;

#[test]
fn test_write_merge() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) -> i32 {
            if b {
                *p = 0;
            } else {
                *p = 1;
            }
            *p
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![2]);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_write() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) -> i32 {
            if b {
                *p = 0;
            }
            *p
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
fn test_write_weak() {
    let code = "
        unsafe fn f(b1: bool, b2: bool, p: *mut i32, q: *mut i32) -> i32 {
            if b1 {
                *p = 0;
            } else {
                let r = if b2 { p } else { q };
                *r = 1;
            }
            *p
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![3]);

    assert_eq!(as_int(ret(&result[1])), vec![0]);
    assert_eq!(result[1].writes.len(), 1);
    assert_eq!(result[1].writes.as_vec()[0].0, vec![3]);
    assert_eq!(result[1].reads.len(), 0);
}

#[test]
fn test_read_merge() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) -> i32 {
            let mut x = 0;
            let mut y = 0;
            if b {
                x = *p;
            } else {
                y = *p;
            }
            x
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
fn test_read() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) -> i32 {
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
fn test_read_weak() {
    let code = "
        unsafe fn f(b1: bool, b2: bool, p: *mut i32, q: *mut i32) -> i32 {
            let mut x = 0;
            let mut y = 0;
            if b1 {
                x = *p;
            } else {
                let r = if b2 { p } else { q };
                y = *r;
            }
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![3]);

    assert_eq!(as_int(ret(&result[1])), vec![0]);
    assert_eq!(result[1].writes.len(), 0);
    assert_eq!(result[1].reads.len(), 2);
    assert_eq!(result[1].reads.as_vec()[0].0, vec![3]);
    assert_eq!(result[1].reads.as_vec()[1].0, vec![4]);
}

#[test]
fn test_read_write() {
    let code = "
        unsafe fn f(p: *mut i32) -> i32 {
            let x = *p;
            *p = 1;
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![1]);
}

#[test]
fn test_write2() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32, q: *mut i32) -> i32 {
            if b {
                *p = 0;
            } else {
                *q = 1;
            }
            0
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![2]);
    assert_eq!(result[0].reads.len(), 0);

    assert_eq!(as_int(ret(&result[1])), vec![0]);
    assert_eq!(result[1].writes.len(), 1);
    assert_eq!(result[1].writes.as_vec()[0].0, vec![3]);
    assert_eq!(result[1].reads.len(), 0);
}

#[test]
fn test_read2() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32, q: *mut i32) -> i32 {
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
    assert_eq!(result[0].reads.as_vec()[0].0, vec![2]);

    assert!(ret(&result[1]).intv.is_top());
    assert_eq!(result[1].writes.len(), 0);
    assert_eq!(result[1].reads.len(), 1);
    assert_eq!(result[1].reads.as_vec()[0].0, vec![3]);
}

#[test]
fn test_write_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(b: bool, p: *mut S) -> i32 {
            if b {
                (*p).x = 0;
            } else {
                (*p).y = 0;
            }
            0
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![2, 0]);
    assert_eq!(result[0].reads.len(), 0);

    assert_eq!(as_int(ret(&result[1])), vec![0]);
    assert_eq!(result[1].writes.len(), 1);
    assert_eq!(result[1].writes.as_vec()[0].0, vec![2, 1]);
    assert_eq!(result[1].reads.len(), 0);
}

#[test]
fn test_write_struct_assign() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(p: *mut S) -> i32 {
            *p = S { x: 0, y: 0 };
            (*p).x + (*p).y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 2);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![1, 0]);
    assert_eq!(result[0].writes.as_vec()[1].0, vec![1, 1]);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_read_write_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(p: *mut S) -> i32 {
            let y = (*p).x;
            *p = S { x: 0, y };
            0
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![1, 1]);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![1, 0]);
}

#[test]
fn test_write_read_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        unsafe fn f(p: *mut S) -> i32 {
            (*p).x = 0;
            let s = *p;
            s.x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![1, 0]);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![1, 1]);
}

#[test]
fn test_write_array() {
    let code = "
        unsafe fn f(p: *mut [i32; 2]) -> i32 {
            (*p)[0] = 0;
            0
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_read_array() {
    let code = "
        unsafe fn f(p: *mut [i32; 2]) -> i32 {
            (*p)[0]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![1]);
}

#[test]
fn test_write_struct2_assign() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        unsafe fn f(p: *mut S) -> i32 {
            *p = S { x: T { x: 0, y: 0 }, y: T { x: 0, y: 0 } };
            0
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 4);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![1, 0, 0]);
    assert_eq!(result[0].writes.as_vec()[1].0, vec![1, 0, 1]);
    assert_eq!(result[0].writes.as_vec()[2].0, vec![1, 1, 0]);
    assert_eq!(result[0].writes.as_vec()[3].0, vec![1, 1, 1]);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_write_read_write_struct2() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        unsafe fn f(p: *mut S) -> i32 {
            (*p).x.x = 0;
            let t: T = (*p).x;
            *p = S { x: T { x: 0, y: 0 }, y: T { x: 0, y: 0 } };
            t.x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(as_int(ret(&result[0])), vec![0]);
    assert_eq!(result[0].writes.len(), 3);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![1, 0, 0]);
    assert_eq!(result[0].writes.as_vec()[1].0, vec![1, 1, 0]);
    assert_eq!(result[0].writes.as_vec()[2].0, vec![1, 1, 1]);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![1, 0, 1]);
}

#[test]
fn test_div() {
    let code = "
        unsafe fn f(n: i32, d: i32, q: *mut i32) -> i32 {
            if d == 0 {
                return -1;
            }
            *q = n / d;
            0
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 2);

    assert_eq!(as_int(ret(&result[0])), vec![-1]);
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 0);

    assert_eq!(as_int(ret(&result[1])), vec![0]);
    assert_eq!(result[1].writes.len(), 1);
    assert_eq!(result[1].writes.as_vec()[0].0, vec![3]);
    assert_eq!(result[1].reads.len(), 0);
}

#[test]
fn test_realloc() {
    let code = "
        extern crate libc;
        extern \"C\" {
            fn realloc(_: *mut libc::c_void, _: libc::c_ulong) -> *mut libc::c_void;
        }
        unsafe fn f(p: *mut i32) {
            realloc(p as *mut libc::c_void, 4);
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_getgroups() {
    let code = "
        extern crate libc;
        extern \"C\" {
            fn getgroups(__size: libc::c_int, __list: *mut __gid_t) -> libc::c_int;
        }
        unsafe fn f(n: i32, p: *mut i32) {
            getgroups(n, p as *mut _);
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![2]);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_unknown_read() {
    let code = "
        extern \"C\" {
            fn unknown(_: *const i32);
        }
        unsafe fn f(p: *mut i32) {
            unknown(p);
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![1]);
}

#[test]
fn test_unknown_file() {
    let code = "
        struct _IO_FILE { x: i32 }
        type FILE = _IO_FILE;
        extern \"C\" {
            fn unknown(_: *mut FILE);
        }
        unsafe fn f(p: *mut FILE) {
            unknown(p);
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_recursive() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) {
            if b {
                f(b, p);
            } else {
                *p = 1;
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![2]);
    assert_eq!(result[0].reads.len(), 0);
}

#[test]
fn test_mutually_recursive() {
    let code = "
        unsafe fn f(b: bool, p: *mut i32) {
            if b {
                g(b, p);
            } else {
                *p = 1;
            }
        }
        unsafe fn g(b: bool, p: *mut i32) {
            if b {
                f(b, p);
            } else {
                *p = 1;
            }
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);

    assert_eq!(result[0].writes.len(), 1);
    assert_eq!(result[0].writes.as_vec()[0].0, vec![2]);
    assert_eq!(result[0].reads.len(), 0);
}

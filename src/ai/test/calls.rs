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
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 1);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![2]);
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
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 2);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![1]);
    assert_eq!(result[0].reads.as_vec()[1].0, vec![2]);
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
    assert_eq!(result.len(), 1);

    assert!(ret(&result[0]).intv.is_top());
    assert_eq!(result[0].writes.len(), 0);
    assert_eq!(result[0].reads.len(), 2);
    assert_eq!(result[0].reads.as_vec()[0].0, vec![2]);
    assert_eq!(result[0].reads.as_vec()[1].0, vec![3]);
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

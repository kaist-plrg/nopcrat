use super::*;

#[test]
fn test_1() {
    let code = "
        struct S { x: i32, y: i32 }
        fn f(b: bool) -> i32 {
            let mut s = S { x: 0, y: 0 };
            s.x = if b { 0 } else { 1 };
            s.y = if b { 0 } else { 2 };
            s.x + s.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_2() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        fn f(b: bool) -> i32 {
            let mut s = S { x: T { x: 0, y: 0 }, y: T { x: 0, y: 0 } };
            s.x.x = if b { 0 } else { 1 };
            s.x.y = if b { 0 } else { 2 };
            s.y.x = if b { 0 } else { 3 };
            s.y.y = if b { 0 } else { 4 };
            s.x.x + s.x.y + s.y.x + s.y.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_1_param() {
    let code = "
        struct S { x: i32, y: i32 }
        fn f(b: bool, mut s: S) -> i32 {
            s.x = if b { 0 } else { 1 };
            s.y = if b { 0 } else { 2 };
            s.x + s.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_2_param() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        fn f(b: bool, mut s: S) -> i32 {
            s.x.x = if b { 0 } else { 1 };
            s.x.y = if b { 0 } else { 2 };
            s.y.x = if b { 0 } else { 3 };
            s.y.y = if b { 0 } else { 4 };
            s.x.x + s.x.y + s.y.x + s.y.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_1_assign() {
    let code = "
        struct S { x: i32, y: i32 }
        fn f(b: bool, mut s: S) -> i32 {
            let x = if b { 0 } else { 1 };
            let y = if b { 0 } else { 2 };
            s = S { x, y };
            s.x + s.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_2_assign() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        fn f(b: bool, mut s: S) -> i32 {
            let v1 = if b { 0 } else { 1 };
            let v2 = if b { 0 } else { 2 };
            let v3 = if b { 0 } else { 3 };
            let v4 = if b { 0 } else { 4 };
            s.x = T { x: v1, y: v2 };
            s.y = T { x: v3, y: v4 };
            s.x.x + s.x.y + s.y.x + s.y.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_2_assign_2() {
    let code = "
        struct S { x: T, y: T }
        struct T { x: i32, y: i32 }
        fn f(b: bool, mut s: S) -> i32 {
            let v1 = if b { 0 } else { 1 };
            let v2 = if b { 0 } else { 2 };
            let v3 = if b { 0 } else { 3 };
            let v4 = if b { 0 } else { 4 };
            let x = T { x: v1, y: v2 };
            let y = T { x: v3, y: v4 };
            s = S { x, y };
            s.x.x + s.x.y + s.y.x + s.y.y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_array() {
    let code = "
        struct S { x: [i32; 2], y: [i32; 2] }
        fn f(b: bool) -> i32 {
            let mut s = S { x: [0, 0], y: [0, 0] };
            s.x[0] = if b { 0 } else { 1 };
            s.x[1] = if b { 0 } else { 2 };
            s.y[0] = if b { 0 } else { 3 };
            s.y[1] = if b { 0 } else { 4 };
            s.x[0] + s.x[1] + s.y[0] + s.y[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

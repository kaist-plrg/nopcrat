use super::*;

#[test]
fn test_1() {
    let code = "
        fn f(b: bool) -> i32 {
            let mut arr = [0, 0];
            arr[0] = if b { 0 } else { 1 };
            arr[1] = if b { 0 } else { 2 };
            arr[0] + arr[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_1_agg() {
    let code = "
        fn f(b: bool) -> i32 {
            let mut arr = [0; 2];
            arr[0] = if b { 0 } else { 1 };
            arr[1] = if b { 0 } else { 2 };
            arr[0] + arr[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_2() {
    let code = "
        fn f(b: bool) -> i32 {
            let mut arr = [[0, 0], [0, 0]];
            arr[0][0] = if b { 0 } else { 1 };
            arr[0][1] = if b { 0 } else { 2 };
            arr[1][0] = if b { 0 } else { 3 };
            arr[1][1] = if b { 0 } else { 4 };
            arr[0][0] + arr[0][1] + arr[1][0] + arr[1][1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_2_agg() {
    let code = "
        fn f(b: bool) -> i32 {
            let mut arr = [[0; 2]; 2];
            arr[0][0] = if b { 0 } else { 1 };
            arr[0][1] = if b { 0 } else { 2 };
            arr[1][0] = if b { 0 } else { 3 };
            arr[1][1] = if b { 0 } else { 4 };
            arr[0][0] + arr[0][1] + arr[1][0] + arr[1][1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_1_param() {
    let code = "
        fn f(b: bool, mut arr: [i32; 2]) -> i32 {
            arr[0] = if b { 0 } else { 1 };
            arr[1] = if b { 0 } else { 2 };
            arr[0] + arr[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_2_param() {
    let code = "
        fn f(b: bool, mut arr: [[i32; 2]; 2]) -> i32 {
            arr[0][0] = if b { 0 } else { 1 };
            arr[0][1] = if b { 0 } else { 2 };
            arr[1][0] = if b { 0 } else { 3 };
            arr[1][1] = if b { 0 } else { 4 };
            arr[0][0] + arr[0][1] + arr[1][0] + arr[1][1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_1_assign() {
    let code = "
        fn f(b: bool, mut arr: [i32; 2]) -> i32 {
            let x = if b { 0 } else { 1 };
            let y = if b { 0 } else { 2 };
            arr = [x, y];
            arr[0] + arr[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2, 3]);
}

#[test]
fn test_2_assign() {
    let code = "
        fn f(b: bool, mut arr: [[i32; 2]; 2]) -> i32 {
            let v1 = if b { 0 } else { 1 };
            let v2 = if b { 0 } else { 2 };
            let v3 = if b { 0 } else { 3 };
            let v4 = if b { 0 } else { 4 };
            arr[0] = [v1, v2];
            arr[1] = [v3, v4];
            arr[0][0] + arr[0][1] + arr[1][0] + arr[1][1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_2_assign_2() {
    let code = "
        fn f(b: bool, mut arr: [[i32; 2]; 2]) -> i32 {
            let v1 = if b { 0 } else { 1 };
            let v2 = if b { 0 } else { 2 };
            let v3 = if b { 0 } else { 3 };
            let v4 = if b { 0 } else { 4 };
            arr = [[v1, v2], [v3, v4]];
            arr[0][0] + arr[0][1] + arr[1][0] + arr[1][1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_struct() {
    let code = "
        struct S { x: i32, y: i32 }
        fn f(b: bool) -> i32 {
            let mut arr = [S { x: 0, y: 0 }, S { x: 0, y: 0 }];
            arr[0].x = if b { 0 } else { 1 };
            arr[0].y = if b { 0 } else { 2 };
            arr[1].x = if b { 0 } else { 3 };
            arr[1].y = if b { 0 } else { 4 };
            arr[0].x + arr[0].y + arr[1].x + arr[1].y
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), (0..=10).collect::<Vec<_>>());
}

#[test]
fn test_weak_update() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut arr: [i32; 2] = [0, 0];
            let p: *mut i32 = &mut arr[0];
            let q: *mut i32 = &mut arr[1];
            let r = if b { p } else { q };
            *r = 1;
            arr[0] + arr[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2]);
}

#[test]
fn test_weak_update_ind_param() {
    let code = "
        unsafe fn f(n: usize) -> i32 {
            let mut arr: [i32; 2] = [0, 0];
            arr[n] = 1;
            arr[0] + arr[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2]);
}

#[test]
fn test_weak_update_ind() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut arr: [i32; 2] = [0, 0];
            let n = if b { 0 } else { 1 };
            arr[n] = 1;
            arr[0] + arr[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1, 2]);
}

#[test]
fn test_weak_update_ind_oob() {
    let code = "
        unsafe fn f(b: bool) -> i32 {
            let mut arr: [i32; 2] = [0, 0];
            let n = if b { 0 } else { 2 };
            arr[n] = 1;
            arr[0] + arr[1]
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0, 1]);
}

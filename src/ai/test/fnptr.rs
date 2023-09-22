use super::*;

#[test]
fn test_none() {
    let code = "
        fn f(mut x: Option::<fn() -> i32>) -> Option::<fn() -> i32> {
            x = None;
            x
        }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    is_none(ret(&result[0]));
}

#[test]
fn test_some() {
    let code = "
        fn f(mut x: Option::<fn() -> i32>) -> Option::<fn() -> i32> {
            x = Some(g);
            x
        }
        fn g() -> i32 { 0 }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_fn(as_some(ret(&result[0]))).len(), 1);
}

use super::*;

#[test]
fn test_return_value() {
    let code = "
        fn f() -> i32 {
            g()
        }
        fn g() -> i32 { 0 }
    ";
    let result = analyze(code);
    assert_eq!(result.len(), 1);
    assert_eq!(as_int(ret(&result[0])), vec![0]);
}

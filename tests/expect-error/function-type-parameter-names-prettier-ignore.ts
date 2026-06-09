// Test that function types require parameter names

// @skjs-expect-error ':' expected
type F1 = (number) => void;

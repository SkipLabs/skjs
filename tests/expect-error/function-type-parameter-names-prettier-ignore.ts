// Test that function types require parameter names

// @ts-expect-error Expected token :
type F1 = (number) => void;

// Simple bigint test
function testBigInt(): void {
  const x: bigint = 123n;
  const y: bigint = BigInt(456);
  console.log(x + y);
}

testBigInt();

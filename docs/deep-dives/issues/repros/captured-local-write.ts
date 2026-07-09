// repro for: captured-local-writes-unchecked (docs/deep-dives/issues/captured-local-writes-unchecked.md)
// pin: 9108f339
// expect: accepted   (skjs check exits 0 — the unsound acceptance at the pin)
// run: make check-file-in-docker FILE=docs/deep-dives/issues/repros/captured-local-write.ts BIN=target/host/dev/skjs

function t(): void {
  let x: string = "a";
  const g = () => {
    x = 5;
  };
  g();
  console.log(x.length);
}
t();

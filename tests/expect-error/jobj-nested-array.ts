// Regression: nested types with array fields whose element type also has a
// string index signature should not OOM the type checker.

import type { Json } from "@skipruntime/core";

type Panel = {
  readonly title: string;
} & { readonly [key: string]: Json | null };

type Dashboard = {
  readonly panels: Panel[];
} & { readonly [key: string]: Json | null };

interface JObj {
  readonly [key: string]: Json | null;
}

declare function f<V extends JObj>(initial: V[]): void;

function test(): void {
  const x: Dashboard[] = [];
  f<Dashboard>(x);
}

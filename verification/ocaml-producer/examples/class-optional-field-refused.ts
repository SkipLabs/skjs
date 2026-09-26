// An optional field without an initializer holds `undefined` from the
// instance's creation, which the exact reading of `label?: string` does not
// admit; `label?: string | undefined` states it.
export class Tagged {
  count: number = 0;
  label?: string;
}

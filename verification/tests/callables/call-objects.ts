/**
 * An object holds both an ordinary method and an arrow. Extracting the method
 * and using .call supplies a different receiver; .call on the arrow preserves
 * its lexical capture. The result is true for either seed.
 *
 * SKJS checks this example, but the independent verifier does not yet model
 * multi-field objects or receiver-dependent methods. Local-arrow .call is
 * covered separately in receiver-call.ts.
 */
function callObjects(seed: boolean): boolean {
  const owner = {
    value: seed,
    choose(this: { value: boolean }, first: boolean, second: boolean): boolean {
      return this.value ? first : second;
    },
    read: (): boolean => seed,
  };
  const receiver: { value: boolean } = { value: !seed };
  const method = owner.choose;
  const rebound: boolean = method.call(receiver, true, false);
  const lexical: boolean = owner.read.call(receiver);
  return rebound ? !lexical : lexical;
}

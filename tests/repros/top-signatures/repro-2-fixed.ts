// Fixed version of repro-2: Invalid implements variance issue
//
// Change from original:
// - Resource is parameterized by K, V instead of returning EagerCollection<Json, Json>
//
// Expected:
// - tsc: OK
// - skjs: OK

// Minimal Json type (enough to include boolean + string)
type Json = boolean | number | string;

// Interface with a method parameter that makes K appear in parameter position.
interface EagerCollection<K extends Json, V extends Json> {
  getArray(key: K): V[];
}

// CHANGED: Resource parameterized by K, V - no widening to Json
interface Resource<K extends Json, V extends Json> {
  instantiate(): EagerCollection<K, V>;
}

// Now this works: K=string, V=Json - exact types, no variance issue
class GoodResource implements Resource<string, Json> {
  instantiate(): EagerCollection<string, Json> {
    return {
      getArray(_key: string): Json[] {
        const result: Json[] = new Array<Json>();
        return result;
      },
    };
  }
}

function test(): void {
  const resource: Resource<string, Json> = new GoodResource();
  console.log(resource);
}

test();

// A mapper producing Serializable records, passed to EagerCollection.map.
// map's V2 is bounded here by the DepSafe that EagerCollection intersects its
// values with, and an unmanaged object is not DepSafe: the call waits for the
// exact meet of a type parameter with a ground type.
import type {
  Context,
  EagerCollection,
  Json,
  Mapper,
  Values,
} from "@skipruntime/core";
type Serializable<T> = T & { readonly [key: string]: Json };
type Todo = { readonly title: string; readonly done: boolean };

class ToTodo implements Mapper<string, string, string, Serializable<Todo>> {
  mapEntry(
    key: string,
    values: Values<string>,
    _context: Context,
  ): Iterable<[string, Serializable<Todo>]> {
    return [[key, { title: values.getUnique(), done: false }]];
  }
}

export function todos(
  c: EagerCollection<string, string>,
): EagerCollection<string, Serializable<Todo>> {
  return c.map(ToTodo);
}

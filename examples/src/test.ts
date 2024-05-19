import { array } from "./skjs.ts";

type list<T> = null | { head: T, tail: list<T> };

function reverse<T>(l: list<T>): list<T> {
  let result = null;
  while(l !== null) {
    result = { head: l.head, tail: result };
    l = l.tail;
  };
  return result
}

function list<T>(...elts: T[]): list<T> {
  let result = null;
  for(let i = 0; i < elts.length; i++) {
    result = { head: elts[i], tail: result };
  }
  return reverse(result);
}



function myObject(): { field1: number } {
  let obj = {};
  obj.field1 = 0;
  return obj;
}

function main(): void {
  console.log(list(1, 2, true));
}

main();


import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  BookId,
  BookValue,
  LoanId,
  LoanValue,
} from "./types.js";


export type Inputs = {
  books: InputDefinition<BookId, BookValue>;
  loans: InputDefinition<LoanId, LoanValue>;
};

export type InputCollections = {
  books: EagerCollection<BookId, BookValue>;
  loans: EagerCollection<LoanId, LoanValue>;
};

export type GraphCollections = {
  books: EagerCollection<BookId, BookValue>;
  loans: EagerCollection<LoanId, LoanValue>;
};

export type Resources = {
  [name: string]: ResourceClass<GraphCollections, Json>;
};

export class AvailableBooksMapper implements Mapper<BookId, BookValue, BookId, BookValue> {
  constructor() {
  }

  mapEntry(
    key: BookId,
    values: Values<BookValue>,
    _context: Context
  ): Iterable<[BookId, BookValue]> {
    const result: Array<[BookId, BookValue]> = Array.of();
    for (const v of values) {
      if (v.available === 1) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class BooksResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<BookId, BookValue> {
    return cs.books;
  }
}

export class BooksAvailableResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<BookId, BookValue> {
    return cs.books.map(AvailableBooksMapper);
  }
}

export const AvailableBooksResource = BooksAvailableResource;

export class LoansResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<LoanId, LoanValue> {
    return cs.loans;
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
            this.inputs = { books: new InputDefinition<BookId, BookValue>([]), loans: new InputDefinition<LoanId, LoanValue>([]) };
    this.resources = { 
      "books": BooksResource, 
      "books-available": BooksAvailableResource, 
      "loans": LoansResource,
      "availableBooks": BooksAvailableResource
    };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { books: inputs.books, loans: inputs.loans };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}

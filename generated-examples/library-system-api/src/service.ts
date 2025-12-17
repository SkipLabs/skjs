import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values
} from "@skipruntime/core";

import type {
  BookId,
  BookValue,
  LoanId,
  LoanValue,
} from "./types.js";


type Inputs = {
  books: Entry<BookId, BookValue>[];
  loans: Entry<LoanId, LoanValue>[];
};

export type InputCollections = {
  books: EagerCollection<BookId, BookValue>;
  loans: EagerCollection<LoanId, LoanValue>;
};

export type GraphCollections = {
  books: EagerCollection<BookId, BookValue>;
  loans: EagerCollection<LoanId, LoanValue>;
};

type Resources = {
  [name: string]: new (params: Json) => Resource<GraphCollections>;
};

export class AvailableBooksMapper implements Mapper<BookId, BookValue, BookId, BookValue> {
  constructor() {
  }

  mapEntry(
    key: BookId,
    values: Values<BookValue>,
    _context: Context
  ): Iterable<[BookId, BookValue]> {
    const arr = values.toArray();
    const result: Array<[BookId, BookValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
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

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyBooks: Entry<BookId, BookValue>[] = Array.of();
    const emptyLoans: Entry<LoanId, LoanValue>[] = Array.of();
    this.initialData = { books: emptyBooks, loans: emptyLoans };
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

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}

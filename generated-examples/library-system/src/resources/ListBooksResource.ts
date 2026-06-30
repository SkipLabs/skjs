import { AssembleBookMapper } from "../mappers/AssembleBookMapper.js";
import type { Book_skip_id_, Book_skip_value_, Book } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListBooksResourceInputs extends SharedCollections {
  readonly books: EagerCollection<Book_skip_id_, Book_skip_value_>;
}

export class ListBooksResource implements Resource<ListBooksResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListBooksResourceInputs,
    _context: Context,
  ): EagerCollection<Book_skip_id_, Book> {
    return inputs.books.map(AssembleBookMapper);
  }
}

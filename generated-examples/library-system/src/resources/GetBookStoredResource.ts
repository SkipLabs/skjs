import type { Book_skip_id_, BookStored, Book } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetBookStoredResourceInputs extends SharedCollections {
  readonly booksStored: EagerCollection<Book_skip_id_, BookStored>;
}

export class GetBookStoredResource implements Resource<GetBookStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetBookStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Book_skip_id_, BookStored> {
    return inputs.booksStored;
  }
}

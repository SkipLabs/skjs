import { GetBookMapper } from "../mappers/GetBookMapper.js";
import type {
  Book_skip_id_,
  Book_skip_value_,
  Book,
  GetBookParams,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetBookResourceInputs extends SharedCollections {
  readonly books: EagerCollection<Book_skip_id_, Book_skip_value_>;
}

export class GetBookResource implements Resource<GetBookResourceInputs> {
  private readonly bookId: string;

  constructor(params: GetBookParams) {
    this.bookId = params.bookId;
  }

  instantiate(
    inputs: GetBookResourceInputs,
    _context: Context,
  ): EagerCollection<0, Book> {
    return inputs.books.map(GetBookMapper, this.bookId);
  }
}

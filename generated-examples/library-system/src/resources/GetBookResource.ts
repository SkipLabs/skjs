import { EnrichBookWithAvailableCopiesMapper } from "../mappers/EnrichBookWithAvailableCopiesMapper.js";
import type {
  Book_skip_id_,
  ActiveLoanCount,
  BookStored,
  Book_skip_value_,
  Book,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetBookResourceInputs extends SharedCollections {
  readonly activeLoanCountByBook: EagerCollection<
    Book_skip_id_,
    ActiveLoanCount
  >;
  readonly booksStored: EagerCollection<Book_skip_id_, BookStored>;
}

export class GetBookResource implements Resource<GetBookResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetBookResourceInputs,
    _context: Context,
  ): EagerCollection<Book_skip_id_, Book_skip_value_> {
    return inputs.booksStored.map(
      EnrichBookWithAvailableCopiesMapper,
      inputs.activeLoanCountByBook,
    );
  }
}

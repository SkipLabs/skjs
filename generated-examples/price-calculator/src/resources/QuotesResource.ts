import type { Quote_skip_id_, QuoteStored, Quote } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface QuotesResourceInputs extends SharedCollections {
  readonly quotes: EagerCollection<Quote_skip_id_, QuoteStored>;
}

export class QuotesResource implements Resource<QuotesResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: QuotesResourceInputs,
    _context: Context,
  ): EagerCollection<Quote_skip_id_, QuoteStored> {
    return inputs.quotes;
  }
}

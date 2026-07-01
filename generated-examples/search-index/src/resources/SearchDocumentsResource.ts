import type { Post_skip_id_, SearchDocument, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface SearchDocumentsResourceInputs extends SharedCollections {
  readonly searchDocuments: EagerCollection<Post_skip_id_, SearchDocument>;
}

export class SearchDocumentsResource implements Resource<SearchDocumentsResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: SearchDocumentsResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, SearchDocument> {
    return inputs.searchDocuments;
  }
}

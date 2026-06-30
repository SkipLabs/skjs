import type { Post_skip_id_, SearchDocument, Post } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetSearchDocumentByPostIdResourceInputs extends SharedCollections {
  readonly searchDocumentsByPostId: EagerCollection<
    Post_skip_id_,
    SearchDocument
  >;
}

export class GetSearchDocumentByPostIdResource implements Resource<GetSearchDocumentByPostIdResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetSearchDocumentByPostIdResourceInputs,
    _context: Context,
  ): EagerCollection<Post_skip_id_, SearchDocument> {
    return inputs.searchDocumentsByPostId;
  }
}

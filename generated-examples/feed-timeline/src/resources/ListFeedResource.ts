import type { FeedItemKey, FeedItem } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListFeedResourceInputs extends SharedCollections {
  readonly feedItems: EagerCollection<FeedItemKey, FeedItem>;
}

export class ListFeedResource implements Resource<ListFeedResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListFeedResourceInputs,
    _context: Context,
  ): EagerCollection<FeedItemKey, FeedItem> {
    return inputs.feedItems;
  }
}

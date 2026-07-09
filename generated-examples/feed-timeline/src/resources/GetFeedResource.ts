import type { FeedEventId, FeedEvent } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetFeedResourceInputs extends SharedCollections {
  readonly feedEvents: EagerCollection<FeedEventId, FeedEvent>;
}

export class GetFeedResource implements Resource<GetFeedResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetFeedResourceInputs,
    _context: Context,
  ): EagerCollection<FeedEventId, FeedEvent> {
    return inputs.feedEvents;
  }
}

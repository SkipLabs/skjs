import type { SubjectIdKey, RatingSummaryAccum } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetSubjectRatingSummaryResourceInputs extends SharedCollections {
  readonly ratingSummaryBySubject: EagerCollection<
    SubjectIdKey,
    RatingSummaryAccum
  >;
}

export class GetSubjectRatingSummaryResource implements Resource<GetSubjectRatingSummaryResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetSubjectRatingSummaryResourceInputs,
    _context: Context,
  ): EagerCollection<SubjectIdKey, RatingSummaryAccum> {
    return inputs.ratingSummaryBySubject;
  }
}

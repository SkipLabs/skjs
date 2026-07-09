import type { Subject_skip_id_, SubjectStored, Subject } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface GetSubjectStoredResourceInputs extends SharedCollections {
  readonly subjects: EagerCollection<Subject_skip_id_, SubjectStored>;
}

export class GetSubjectStoredResource implements Resource<GetSubjectStoredResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: GetSubjectStoredResourceInputs,
    _context: Context,
  ): EagerCollection<Subject_skip_id_, SubjectStored> {
    return inputs.subjects;
  }
}

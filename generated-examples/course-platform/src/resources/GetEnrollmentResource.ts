import type {
  EnrollmentKey,
  Enrollment_skip_value_,
  Enrollment,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface GetEnrollmentResourceInputs extends SharedCollections {
  readonly enrollments: EagerCollection<EnrollmentKey, Enrollment_skip_value_>;
}

export class GetEnrollmentResource implements Resource<GetEnrollmentResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: GetEnrollmentResourceInputs,
    _context: Context,
  ): EagerCollection<EnrollmentKey, Enrollment_skip_value_> {
    return inputs.enrollments;
  }
}

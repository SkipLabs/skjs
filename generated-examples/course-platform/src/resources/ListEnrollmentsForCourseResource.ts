import { EnrollmentsByCourseMapper } from "../mappers/EnrollmentsByCourseMapper.js";
import type {
  EnrollmentKey,
  Enrollment_skip_value_,
  Course_skip_id_,
  EnrollmentByCourseValue,
  Enrollment,
  Course,
} from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
} from "@skipruntime/core";

export interface ListEnrollmentsForCourseResourceInputs extends SharedCollections {
  readonly enrollments: EagerCollection<EnrollmentKey, Enrollment_skip_value_>;
}

export class ListEnrollmentsForCourseResource implements Resource<ListEnrollmentsForCourseResourceInputs> {
  constructor(_params: {}) {}

  instantiate(
    inputs: ListEnrollmentsForCourseResourceInputs,
    _context: Context,
  ): EagerCollection<Course_skip_id_, EnrollmentByCourseValue> {
    const enrollmentsByCourse = inputs.enrollments.map(
      EnrollmentsByCourseMapper,
    );
    return enrollmentsByCourse;
  }
}

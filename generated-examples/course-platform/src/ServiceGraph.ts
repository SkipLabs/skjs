import type {
  Course_skip_id_,
  Course,
  Course_skip_value_,
  EnrollmentKey,
  Enrollment_skip_value_,
  Enrollment,
  LessonKey,
  Lesson_skip_value_,
  Lesson,
  User_skip_id_,
  User,
  User_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly courses: EagerCollection<Course_skip_id_, Course_skip_value_>;
  readonly enrollments: EagerCollection<EnrollmentKey, Enrollment_skip_value_>;
  readonly lessons: EagerCollection<LessonKey, Lesson_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly courses: EagerCollection<Course_skip_id_, Course_skip_value_>;
  readonly enrollments: EagerCollection<EnrollmentKey, Enrollment_skip_value_>;
  readonly lessons: EagerCollection<LessonKey, Lesson_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_courses = inputs.courses;
  const output_enrollments = inputs.enrollments;
  const output_lessons = inputs.lessons;
  const output_users = inputs.users;
  return {
    courses: output_courses,
    enrollments: output_enrollments,
    lessons: output_lessons,
    users: output_users,
  };
}

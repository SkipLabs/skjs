import { AssembleCourseWithCountsMapper } from "./mappers/AssembleCourseWithCountsMapper.js";
import { EnrollmentByCourseMapper } from "./mappers/EnrollmentByCourseMapper.js";
import { EnrollmentByUserMapper } from "./mappers/EnrollmentByUserMapper.js";
import { EnrollmentCountByCourseMapper } from "./mappers/EnrollmentCountByCourseMapper.js";
import { LessonByCourseWithIdMapper } from "./mappers/LessonByCourseWithIdMapper.js";
import { LessonCountByCourseMapper } from "./mappers/LessonCountByCourseMapper.js";
import type {
  Course_skip_id_,
  Course,
  CourseStored,
  EnrollmentKey,
  Enrollment_skip_value_,
  Enrollment,
  Lesson_skip_id_,
  Lesson,
  Lesson_skip_value_,
  User_skip_id_,
  User,
  User_skip_value_,
  Course_skip_value_,
} from "./types.js";
import type {
  EagerCollection,
  Context,
  NamedEagerCollections,
  SharedCollections,
} from "@skipruntime/core";

export interface InputCollections extends NamedEagerCollections {
  readonly coursesStored: EagerCollection<Course_skip_id_, CourseStored>;
  readonly enrollments: EagerCollection<EnrollmentKey, Enrollment_skip_value_>;
  readonly lessons: EagerCollection<Lesson_skip_id_, Lesson_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly courses: EagerCollection<Course_skip_id_, Course_skip_value_>;
  readonly coursesStored: EagerCollection<Course_skip_id_, CourseStored>;
  readonly enrollments: EagerCollection<EnrollmentKey, Enrollment_skip_value_>;
  readonly enrollmentsByCourse: EagerCollection<Course_skip_id_, Enrollment>;
  readonly enrollmentsByUser: EagerCollection<User_skip_id_, Enrollment>;
  readonly lessons: EagerCollection<Lesson_skip_id_, Lesson_skip_value_>;
  readonly lessonsByCourse: EagerCollection<Course_skip_id_, Lesson>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_enrollmentsByCourse = inputs.enrollments.map(
    EnrollmentByCourseMapper,
  );
  const enrollmentCountByCourse = output_enrollmentsByCourse.map(
    EnrollmentCountByCourseMapper,
  );
  const output_lessonsByCourse = inputs.lessons.map(LessonByCourseWithIdMapper);
  const lessonCountByCourse = output_lessonsByCourse.map(
    LessonCountByCourseMapper,
  );
  const output_courses = inputs.coursesStored.map(
    AssembleCourseWithCountsMapper,
    lessonCountByCourse,
    enrollmentCountByCourse,
  );
  const output_coursesStored = inputs.coursesStored;
  const output_enrollments = inputs.enrollments;
  const output_enrollmentsByUser = inputs.enrollments.map(
    EnrollmentByUserMapper,
  );
  const output_lessons = inputs.lessons;
  const output_users = inputs.users;
  return {
    enrollmentsByCourse: output_enrollmentsByCourse,
    lessonsByCourse: output_lessonsByCourse,
    courses: output_courses,
    coursesStored: output_coursesStored,
    enrollments: output_enrollments,
    enrollmentsByUser: output_enrollmentsByUser,
    lessons: output_lessons,
    users: output_users,
  };
}

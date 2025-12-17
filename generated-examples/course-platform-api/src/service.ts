import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values
} from "@skipruntime/core";

import type {
  CourseId,
  CourseValue,
  LessonId,
  LessonValue,
  EnrollmentId,
  EnrollmentValue,
  CoursesLessonsResourceParams,
  StudentsEnrollmentsResourceParams,
} from "./types.js";


type Inputs = {
  courses: Entry<CourseId, CourseValue>[];
  lessons: Entry<LessonId, LessonValue>[];
  enrollments: Entry<EnrollmentId, EnrollmentValue>[];
};

export type InputCollections = {
  courses: EagerCollection<CourseId, CourseValue>;
  lessons: EagerCollection<LessonId, LessonValue>;
  enrollments: EagerCollection<EnrollmentId, EnrollmentValue>;
};

export type GraphCollections = {
  courses: EagerCollection<CourseId, CourseValue>;
  lessons: EagerCollection<LessonId, LessonValue>;
  enrollments: EagerCollection<EnrollmentId, EnrollmentValue>;
};

type Resources = {
  "courses": new (params: Json) => Resource<GraphCollections>;
  "lessons": new (params: Json) => Resource<GraphCollections>;
  "enrollments": new (params: Json) => Resource<GraphCollections>;
  "courses-lessons": new (params: Json) => Resource<GraphCollections>;
  "students-enrollments": new (params: Json) => Resource<GraphCollections>;
};

export class LessonsByCourseMapper implements Mapper<LessonId, LessonValue, LessonId, LessonValue> {
  private courseId: string;

  constructor(courseId: string) {
    this.courseId = courseId;
  }

  mapEntry(
    key: LessonId,
    values: Values<LessonValue>,
    _context: Context
  ): Iterable<[LessonId, LessonValue]> {
    const result: Array<[LessonId, LessonValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.courseId === this.courseId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class EnrollmentsByStudentMapper implements Mapper<EnrollmentId, EnrollmentValue, EnrollmentId, EnrollmentValue> {
  private studentId: string;

  constructor(studentId: string) {
    this.studentId = studentId;
  }

  mapEntry(
    key: EnrollmentId,
    values: Values<EnrollmentValue>,
    _context: Context
  ): Iterable<[EnrollmentId, EnrollmentValue]> {
    const result: Array<[EnrollmentId, EnrollmentValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.studentId === this.studentId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class CoursesResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CourseId, CourseValue> {
    return cs.courses;
  }
}

export class LessonsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<LessonId, LessonValue> {
    return cs.lessons;
  }
}

export class EnrollmentsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<EnrollmentId, EnrollmentValue> {
    return cs.enrollments;
  }
}

export class CoursesLessonsResource implements Resource<GraphCollections> {
  private courseId: string;

  constructor(params: Json) {
    const typed = params as CoursesLessonsResourceParams;
    this.courseId = typed.courseId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<LessonId, LessonValue> {
    return cs.lessons.map(LessonsByCourseMapper, this.courseId);
  }
}

export class StudentsEnrollmentsResource implements Resource<GraphCollections> {
  private studentId: string;

  constructor(params: Json) {
    const typed = params as StudentsEnrollmentsResourceParams;
    this.studentId = typed.studentId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<EnrollmentId, EnrollmentValue> {
    return cs.enrollments.map(EnrollmentsByStudentMapper, this.studentId);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyCourses: Entry<CourseId, CourseValue>[] = Array.of();
    const emptyLessons: Entry<LessonId, LessonValue>[] = Array.of();
    const emptyEnrollments: Entry<EnrollmentId, EnrollmentValue>[] = Array.of();
    this.initialData = { courses: emptyCourses, lessons: emptyLessons, enrollments: emptyEnrollments };
    this.resources = { "courses": CoursesResource, "lessons": LessonsResource, "enrollments": EnrollmentsResource, "courses-lessons": CoursesLessonsResource, "students-enrollments": StudentsEnrollmentsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { courses: inputs.courses, lessons: inputs.lessons, enrollments: inputs.enrollments };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}

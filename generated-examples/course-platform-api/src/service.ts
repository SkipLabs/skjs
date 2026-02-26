import type {
  EagerCollection,

  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

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


export type Inputs = {
  courses: InputDefinition<CourseId, CourseValue>;
  lessons: InputDefinition<LessonId, LessonValue>;
  enrollments: InputDefinition<EnrollmentId, EnrollmentValue>;
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

export type Resources = {
  "courses": ResourceClass<GraphCollections, {}>;
  "lessons": ResourceClass<GraphCollections, {}>;
  "enrollments": ResourceClass<GraphCollections, {}>;
  "courses-lessons": ResourceClass<GraphCollections, CoursesLessonsResourceParams>;
  "students-enrollments": ResourceClass<GraphCollections, StudentsEnrollmentsResourceParams>;
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
    for (const v of values) {
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
    for (const v of values) {
      if (v.studentId === this.studentId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class CoursesResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CourseId, CourseValue> {
    return cs.courses;
  }
}

export class LessonsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<LessonId, LessonValue> {
    return cs.lessons;
  }
}

export class EnrollmentsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
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

  constructor(params: CoursesLessonsResourceParams) {
    this.courseId = params.courseId;
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

  constructor(params: StudentsEnrollmentsResourceParams) {
    this.studentId = params.studentId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<EnrollmentId, EnrollmentValue> {
    return cs.enrollments.map(EnrollmentsByStudentMapper, this.studentId);
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
                this.inputs = { courses: new InputDefinition<CourseId, CourseValue>([]), lessons: new InputDefinition<LessonId, LessonValue>([]), enrollments: new InputDefinition<EnrollmentId, EnrollmentValue>([]) };
    this.resources = { "courses": CoursesResource, "lessons": LessonsResource, "enrollments": EnrollmentsResource, "courses-lessons": CoursesLessonsResource, "students-enrollments": StudentsEnrollmentsResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { courses: inputs.courses, lessons: inputs.lessons, enrollments: inputs.enrollments };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}

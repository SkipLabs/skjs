import type { InputCollections, GraphCollections } from "./ServiceGraph.js";
import { createGraph } from "./ServiceGraph.js";
import { GetCourseByIdResource } from "./resources/GetCourseByIdResource.js";
import { GetEnrollmentResource } from "./resources/GetEnrollmentResource.js";
import { GetLessonByIdResource } from "./resources/GetLessonByIdResource.js";
import { ListCoursesResource } from "./resources/ListCoursesResource.js";
import { ListEnrollmentsForCourseResource } from "./resources/ListEnrollmentsForCourseResource.js";
import { ListLessonsForCourseResource } from "./resources/ListLessonsForCourseResource.js";
import { ListMyEnrollmentsResource } from "./resources/ListMyEnrollmentsResource.js";
import { getMeResource } from "./resources/getMeResource.js";
import type {
  Course_skip_id_,
  Course_skip_value_,
  EnrollmentKey,
  Enrollment_skip_value_,
  LessonKey,
  Lesson_skip_value_,
  User_skip_id_,
  User_skip_value_,
  ListCoursesParams,
  ListMyEnrollmentsParams,
  Course,
  Enrollment,
  Lesson,
  User,
} from "./types.js";
import type {
  SkipService,
  ResourceClass,
  Context,
  NamedInputDefinitions,
  NamedResources,
  Json,
} from "@skipruntime/core";
import { InputDefinition } from "@skipruntime/core";

interface Inputs extends NamedInputDefinitions {
  readonly courses: InputDefinition<Course_skip_id_, Course_skip_value_>;
  readonly enrollments: InputDefinition<EnrollmentKey, Enrollment_skip_value_>;
  readonly lessons: InputDefinition<LessonKey, Lesson_skip_value_>;
  readonly users: InputDefinition<User_skip_id_, User_skip_value_>;
}

interface Resources extends NamedResources<GraphCollections> {
  readonly getCourseByIdResource: ResourceClass<GraphCollections, Json>;
  readonly getEnrollmentResource: ResourceClass<GraphCollections, Json>;
  readonly getLessonByIdResource: ResourceClass<GraphCollections, Json>;
  readonly listCoursesResource: ResourceClass<
    GraphCollections,
    ListCoursesParams
  >;
  readonly listEnrollmentsForCourseResource: ResourceClass<
    GraphCollections,
    Json
  >;
  readonly listLessonsForCourseResource: ResourceClass<GraphCollections, Json>;
  readonly listMyEnrollmentsResource: ResourceClass<
    GraphCollections,
    ListMyEnrollmentsParams
  >;
  readonly getMeResource: ResourceClass<GraphCollections, Json>;
}

class Service implements SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  readonly inputs: Inputs;
  readonly resources: Resources;

  constructor() {
    this.inputs = {
      courses: new InputDefinition<Course_skip_id_, Course_skip_value_>([]),
      enrollments: new InputDefinition<EnrollmentKey, Enrollment_skip_value_>(
        [],
      ),
      lessons: new InputDefinition<LessonKey, Lesson_skip_value_>([]),
      users: new InputDefinition<User_skip_id_, User_skip_value_>([]),
    };
    this.resources = {
      getCourseByIdResource: GetCourseByIdResource,
      getEnrollmentResource: GetEnrollmentResource,
      getLessonByIdResource: GetLessonByIdResource,
      listCoursesResource: ListCoursesResource,
      listEnrollmentsForCourseResource: ListEnrollmentsForCourseResource,
      listLessonsForCourseResource: ListLessonsForCourseResource,
      listMyEnrollmentsResource: ListMyEnrollmentsResource,
      getMeResource: getMeResource,
    };
  }

  createGraph(inputs: InputCollections, context: Context): GraphCollections {
    return createGraph(inputs, context);
  }
}

export function service(): SkipService<
  Inputs,
  InputCollections,
  GraphCollections
> {
  return new Service();
}

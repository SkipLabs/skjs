export type CourseId = string;

export type CourseValue = {
  title: string;
  description: string;
  instructorId: string;
  createdAt: number | null;
};

export type Course = CourseValue & { id: CourseId };

export type LessonId = string;

export type LessonValue = {
  courseId: string;
  title: string;
  content: string;
  order: number;
};

export type Lesson = LessonValue & { id: LessonId };

export type EnrollmentId = string;

export type EnrollmentValue = {
  studentId: string;
  courseId: string;
  enrolledAt: number;
  progress: number;
};

export type Enrollment = EnrollmentValue & { id: EnrollmentId };

export type CoursesLessonsResourceParams = {
  courseId: string;
};

export type StudentsEnrollmentsResourceParams = {
  studentId: string;
};

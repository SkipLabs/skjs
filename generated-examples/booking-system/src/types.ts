import type { Json } from "@skipruntime/core";

export type ApiError = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly details?: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type Appointment = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly cancelledBy?: string;
  readonly completedAt?: string;
  readonly createdAt: string;
  readonly customerId: string;
  readonly endAt: string;
  readonly id: string;
  readonly notes?: string;
  readonly providerId: string;
  readonly revision: number;
  readonly serviceId: string;
  readonly startAt: string;
  readonly status: AppointmentStatus;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type AppointmentList = {
  readonly items: Appointment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type AppointmentList_skip_id_ = {
  readonly items: Appointment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type AppointmentList_skip_value_ = {
  readonly items: Appointment[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type AppointmentRoleFilter = "customer" | "provider";

export type AppointmentRoleFilter_skip_id_ = "customer" | "provider";

export type AppointmentRoleFilter_skip_value_ = "customer" | "provider";

export type AppointmentStatus = "SCHEDULED" | "CANCELLED" | "COMPLETED";

export type AppointmentStatus_skip_id_ =
  | "SCHEDULED"
  | "CANCELLED"
  | "COMPLETED";

export type AppointmentStatus_skip_value_ =
  | "SCHEDULED"
  | "CANCELLED"
  | "COMPLETED";

export type Appointment_skip_id_ = string;

export type Appointment_skip_value_ = {
  readonly cancellationReason?: string;
  readonly cancelledAt?: string;
  readonly cancelledBy?: string;
  readonly completedAt?: string;
  readonly createdAt: string;
  readonly customerId: string;
  readonly endAt: string;
  readonly notes?: string;
  readonly providerId: string;
  readonly revision: number;
  readonly serviceId: string;
  readonly startAt: string;
  readonly status: AppointmentStatus;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type AppointmentsByServiceParams = { readonly serviceId: string } & {
  readonly [key: string]: Json | null;
};

export type AvailabilityList = { readonly slots: AvailableSlot[] } & {
  readonly [key: string]: Json | null;
};

export type AvailabilityList_skip_id_ = { readonly slots: AvailableSlot[] } & {
  readonly [key: string]: Json | null;
};

export type AvailabilityList_skip_value_ = {
  readonly slots: AvailableSlot[];
} & { readonly [key: string]: Json | null };

export type AvailabilityRule = {
  readonly dayOfWeek: number;
  readonly endTimeMinutes: number;
  readonly startTimeMinutes: number;
  readonly timezone?: string;
} & { readonly [key: string]: Json | null };

export type AvailabilityRule_skip_id_ = {
  readonly dayOfWeek: number;
  readonly endTimeMinutes: number;
  readonly startTimeMinutes: number;
  readonly timezone?: string;
} & { readonly [key: string]: Json | null };

export type AvailabilityRule_skip_value_ = {
  readonly dayOfWeek: number;
  readonly endTimeMinutes: number;
  readonly startTimeMinutes: number;
  readonly timezone?: string;
} & { readonly [key: string]: Json | null };

export type AvailableSlot = {
  readonly endAt: string;
  readonly serviceId: string;
  readonly startAt: string;
} & { readonly [key: string]: Json | null };

export type AvailableSlot_skip_id_ = {
  readonly endAt: string;
  readonly serviceId: string;
  readonly startAt: string;
} & { readonly [key: string]: Json | null };

export type AvailableSlot_skip_value_ = {
  readonly endAt: string;
  readonly serviceId: string;
  readonly startAt: string;
} & { readonly [key: string]: Json | null };

export type CancelAppointmentRequest = {
  readonly cancellationReason?: string;
} & { readonly [key: string]: Json | null };

export type CancelAppointmentRequest_skip_id_ = {
  readonly cancellationReason?: string;
} & { readonly [key: string]: Json | null };

export type CancelAppointmentRequest_skip_value_ = {
  readonly cancellationReason?: string;
} & { readonly [key: string]: Json | null };

export type CreateAppointmentRequest = {
  readonly notes?: string;
  readonly serviceId: string;
  readonly startAt: string;
} & { readonly [key: string]: Json | null };

export type CreateAppointmentRequest_skip_id_ = {
  readonly notes?: string;
  readonly serviceId: string;
  readonly startAt: string;
} & { readonly [key: string]: Json | null };

export type CreateAppointmentRequest_skip_value_ = {
  readonly notes?: string;
  readonly serviceId: string;
  readonly startAt: string;
} & { readonly [key: string]: Json | null };

export type CreateServiceRequest = {
  readonly availabilityRules: AvailabilityRule[];
  readonly currency?: string;
  readonly description?: string;
  readonly durationMinutes: number;
  readonly name: string;
  readonly priceCents?: number;
} & { readonly [key: string]: Json | null };

export type CreateServiceRequest_skip_id_ = {
  readonly availabilityRules: AvailabilityRule[];
  readonly currency?: string;
  readonly description?: string;
  readonly durationMinutes: number;
  readonly name: string;
  readonly priceCents?: number;
} & { readonly [key: string]: Json | null };

export type CreateServiceRequest_skip_value_ = {
  readonly availabilityRules: AvailabilityRule[];
  readonly currency?: string;
  readonly description?: string;
  readonly durationMinutes: number;
  readonly name: string;
  readonly priceCents?: number;
} & { readonly [key: string]: Json | null };

export type GetUserByIdParams = { readonly userId: string } & {
  readonly [key: string]: Json | null;
};

export type ListServicesParams = { readonly providerId?: string } & {
  readonly [key: string]: Json | null;
};

export type RescheduleAppointmentRequest = { readonly startAt: string } & {
  readonly [key: string]: Json | null;
};

export type RescheduleAppointmentRequest_skip_id_ = {
  readonly startAt: string;
} & { readonly [key: string]: Json | null };

export type RescheduleAppointmentRequest_skip_value_ = {
  readonly startAt: string;
} & { readonly [key: string]: Json | null };

export type Service = {
  readonly availabilityRules: AvailabilityRule[];
  readonly createdAt: string;
  readonly currency?: string;
  readonly description?: string;
  readonly durationMinutes: number;
  readonly id: string;
  readonly name: string;
  readonly priceCents?: number;
  readonly providerId: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type ServiceList = {
  readonly items: Service[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type ServiceList_skip_id_ = {
  readonly items: Service[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type ServiceList_skip_value_ = {
  readonly items: Service[];
  readonly total?: number;
} & { readonly [key: string]: Json | null };

export type Service_skip_id_ = string;

export type Service_skip_value_ = {
  readonly availabilityRules: AvailabilityRule[];
  readonly createdAt: string;
  readonly currency?: string;
  readonly description?: string;
  readonly durationMinutes: number;
  readonly name: string;
  readonly priceCents?: number;
  readonly providerId: string;
  readonly updatedAt?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateServiceRequest = {
  readonly availabilityRules?: AvailabilityRule[];
  readonly currency?: string;
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name?: string;
  readonly priceCents?: number;
} & { readonly [key: string]: Json | null };

export type UpdateServiceRequest_skip_id_ = {
  readonly availabilityRules?: AvailabilityRule[];
  readonly currency?: string;
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name?: string;
  readonly priceCents?: number;
} & { readonly [key: string]: Json | null };

export type UpdateServiceRequest_skip_value_ = {
  readonly availabilityRules?: AvailabilityRule[];
  readonly currency?: string;
  readonly description?: string;
  readonly durationMinutes?: number;
  readonly name?: string;
  readonly priceCents?: number;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly avatarUrl?: string;
  readonly bio?: string;
  readonly createdAt?: string;
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

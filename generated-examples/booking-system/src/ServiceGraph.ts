import type {
  Appointment_skip_id_,
  Appointment,
  Appointment_skip_value_,
  AvailabilityWindowKey,
  AvailabilityWindowStored,
  BookableResource_skip_id_,
  BookableResource,
  BookableResource_skip_value_,
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
  readonly appointments: EagerCollection<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
  readonly availabilityWindows: EagerCollection<
    AvailabilityWindowKey,
    AvailabilityWindowStored
  >;
  readonly resources: EagerCollection<
    BookableResource_skip_id_,
    BookableResource_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly appointments: EagerCollection<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
  readonly availabilityWindows: EagerCollection<
    AvailabilityWindowKey,
    AvailabilityWindowStored
  >;
  readonly resources: EagerCollection<
    BookableResource_skip_id_,
    BookableResource_skip_value_
  >;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const output_appointments = inputs.appointments;
  const output_availabilityWindows = inputs.availabilityWindows;
  const output_resources = inputs.resources;
  const output_users = inputs.users;
  return {
    appointments: output_appointments,
    availabilityWindows: output_availabilityWindows,
    resources: output_resources,
    users: output_users,
  };
}

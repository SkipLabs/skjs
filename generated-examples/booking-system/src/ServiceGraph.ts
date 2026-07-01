import { AppointmentByCustomerMapper } from "./mappers/AppointmentByCustomerMapper.js";
import { AppointmentByProviderMapper } from "./mappers/AppointmentByProviderMapper.js";
import type {
  Appointment_skip_id_,
  Appointment,
  Appointment_skip_value_,
  Service_skip_id_,
  Service,
  Service_skip_value_,
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
  readonly services: EagerCollection<Service_skip_id_, Service_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export interface GraphCollections extends SharedCollections {
  readonly appointments: EagerCollection<
    Appointment_skip_id_,
    Appointment_skip_value_
  >;
  readonly appointmentsByCustomer: EagerCollection<User_skip_id_, Appointment>;
  readonly appointmentsByProvider: EagerCollection<User_skip_id_, Appointment>;
  readonly services: EagerCollection<Service_skip_id_, Service_skip_value_>;
  readonly users: EagerCollection<User_skip_id_, User_skip_value_>;
}

export function createGraph(
  inputs: InputCollections,
  _context: Context,
): GraphCollections {
  const appointmentsByCustomer = inputs.appointments.map(
    AppointmentByCustomerMapper,
  );
  const appointmentsByProvider = inputs.appointments.map(
    AppointmentByProviderMapper,
  );
  const output_appointments = inputs.appointments;
  const output_appointmentsByCustomer = appointmentsByCustomer;
  const output_appointmentsByProvider = appointmentsByProvider;
  const output_services = inputs.services;
  const output_users = inputs.users;
  return {
    appointments: output_appointments,
    appointmentsByCustomer: output_appointmentsByCustomer,
    appointmentsByProvider: output_appointmentsByProvider,
    services: output_services,
    users: output_users,
  };
}

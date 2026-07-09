import type { User_skip_id_, Appointment, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface AppointmentsByCustomerResourceInputs extends SharedCollections {
  readonly appointmentsByCustomer: EagerCollection<User_skip_id_, Appointment>;
}

export class AppointmentsByCustomerResource implements Resource<AppointmentsByCustomerResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: AppointmentsByCustomerResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Appointment> {
    return inputs.appointmentsByCustomer;
  }
}

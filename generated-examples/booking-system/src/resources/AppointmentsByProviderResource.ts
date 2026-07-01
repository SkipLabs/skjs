import type { User_skip_id_, Appointment, User } from "../types.js";
import type {
  Resource,
  EagerCollection,
  Context,
  SharedCollections,
  Json,
} from "@skipruntime/core";

export interface AppointmentsByProviderResourceInputs extends SharedCollections {
  readonly appointmentsByProvider: EagerCollection<User_skip_id_, Appointment>;
}

export class AppointmentsByProviderResource implements Resource<AppointmentsByProviderResourceInputs> {
  constructor(_params: Json) {}

  instantiate(
    inputs: AppointmentsByProviderResourceInputs,
    _context: Context,
  ): EagerCollection<User_skip_id_, Appointment> {
    return inputs.appointmentsByProvider;
  }
}

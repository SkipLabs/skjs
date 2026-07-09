import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  Dataset_skip_id_,
  DatasetStored,
  User_skip_id_,
  DatasetByOwnerValue,
  Dataset,
  User,
} from "../types.js";
import type { Context, Mapper, Values } from "@skipruntime/core";

// For each dataset entry, emit one output pair whose key is sourced from the entry's ownerId field (the User primary key), paired with a new value whose id is sourced from the entry's key (the original Dataset primary key) and whose ownerId, name, description, columns, createdAt, updatedAt are sourced from the entry's value. This re-injects the dataset id on the value side so consumers of the re-keyed collection can still reconstruct the full Dataset response.
export class DatasetByOwnerMapper implements Mapper<
  Dataset_skip_id_,
  DatasetStored,
  User_skip_id_,
  DatasetByOwnerValue
> {
  mapEntry(
    key: Dataset_skip_id_,
    values: Values<DatasetStored>,
    context: Context,
  ): Iterable<[User_skip_id_, DatasetByOwnerValue]> {
    // > body
    const emits: [User_skip_id_, DatasetByOwnerValue][] = [];
    for (const value of values) {
      const out: DatasetByOwnerValue = {
        id: key,
        ownerId: value.ownerId,
        name: value.name,
        columns: value.columns,
        createdAt: value.createdAt,
        updatedAt: value.updatedAt,
        ...(value.description !== undefined && {
          description: value.description,
        }),
      };
      emits.push([value.ownerId, out]);
    }
    return emits;
    // < body
  }
}

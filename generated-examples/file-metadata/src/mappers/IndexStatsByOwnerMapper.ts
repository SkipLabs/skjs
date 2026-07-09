import { isJsonObject, isJsonArray } from "../../helpers/index.js";
import type {
  MimeTypeCount,
  User_skip_id_,
  User_skip_value_,
  IndexStatsStored,
  OwnerIdKey,
  IndexedFile,
  OwnerMimeKey,
  MimeCountValue,
  User,
} from "../types.js";
import type {
  Context,
  Mapper,
  Values,
  EagerCollection,
} from "@skipruntime/core";

// For each user entry, consult filesByOwner for the file values indexed by the entry's key (the user id). Compute totalFiles as the count of consulted values (zero when none). Compute totalSizeBytes as the sum of each consulted value's sizeBytes field (zero when none). Compute mimeTypeBreakdown as an array with one MimeTypeCount entry per distinct mimeType field across the consulted values: for each such distinct mimeType, consult mimeCountByOwnerMime with a composite key built from the entry's key (as ownerId) and the mimeType (defaulting to zero when the consultation yields nothing) — sum the consulted numeric values to obtain count. The array is sorted ascending by mimeType (lexicographic) for stability; ties are impossible because each mimeType appears at most once. When no values are consulted from filesByOwner, mimeTypeBreakdown is the empty array. Emit one output pair whose key is the entry's key and whose value is a record enumerating every required field of IndexStatsStored explicitly: totalFiles sourced from the computed count; totalSizeBytes sourced from the computed sum; mimeTypeBreakdown sourced from the computed array. Every User in inputs.users yields exactly one entry.
export class IndexStatsByOwnerMapper implements Mapper<
  User_skip_id_,
  User_skip_value_,
  User_skip_id_,
  IndexStatsStored
> {
  constructor(
    private filesByOwner: EagerCollection<OwnerIdKey, IndexedFile>,
    private mimeCountByOwnerMime: EagerCollection<OwnerMimeKey, MimeCountValue>,
  ) {}

  mapEntry(
    key: User_skip_id_,
    values: Values<User_skip_value_>,
    context: Context,
  ): Iterable<[User_skip_id_, IndexStatsStored]> {
    // > body
    const fileEntries = this.filesByOwner.getArray(key);
    const totalFiles = fileEntries.length;
    let totalSizeBytes = 0;
    const mimeTypesSeen = new Set<string>();
    const distinctMimeTypes: string[] = [];
    for (const file of fileEntries) {
      totalSizeBytes += file.sizeBytes;
      if (!mimeTypesSeen.has(file.mimeType)) {
        mimeTypesSeen.add(file.mimeType);
        distinctMimeTypes.push(file.mimeType);
      }
    }
    distinctMimeTypes.sort((a, b) => (a < b ? -1 : a > b ? 1 : 0));
    const mimeTypeBreakdown: MimeTypeCount[] = [];
    for (const mimeType of distinctMimeTypes) {
      const counts = this.mimeCountByOwnerMime.getArray({
        ownerId: key,
        mimeType,
      });
      let count = 0;
      for (const c of counts) count += c;
      mimeTypeBreakdown.push({ count, mimeType });
    }
    const out: IndexStatsStored = {
      totalFiles,
      totalSizeBytes,
      mimeTypeBreakdown,
    };
    return [[key, out]];
    // < body
  }
}

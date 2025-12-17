import type {
  EagerCollection,
  Entry,
  Json,
  Resource,
  SkipService,
  Context,
  Mapper,
  Values,
  DepSafe
} from "@skipruntime/core";

import type {
  JobId,
  JobValue,
  PendingProcessingo5ljfmEnum,
} from "./types.js";

type JobStatus = PendingProcessingo5ljfmEnum;

type Inputs = {
  jobs: Entry<JobId, JobValue>[];
};

export type InputCollections = {
  jobs: EagerCollection<JobId, JobValue>;
};

export type GraphCollections = {
  jobs: EagerCollection<JobId, JobValue>;
};

type Resources = {
  "jobs": new (params: Json) => Resource<GraphCollections>;
  "jobs-pending": new (params: Json) => Resource<GraphCollections>;
  "jobs-processing": new (params: Json) => Resource<GraphCollections>;
  "jobs-completed": new (params: Json) => Resource<GraphCollections>;
  "jobs-failed": new (params: Json) => Resource<GraphCollections>;
};

export class FilterByStatusMapper implements Mapper<JobId, JobValue, JobId, JobValue> {
  private targetStatus: JobStatus;

  constructor(targetStatus: JobStatus) {
    this.targetStatus = targetStatus;
  }

  mapEntry(
    key: JobId,
    values: Values<JobValue>,
    _context: Context
  ): Iterable<[JobId, JobValue]> {
    const arr = values.toArray();
    const result: Array<[JobId, JobValue]> = Array.of();
    for (let i = 0; i < arr.length; i++) {
      const v = arr[i]!;
      if (v.status === this.targetStatus) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class JobsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs;
  }
}

export class JobsPendingResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs.map(FilterByStatusMapper, "pending" as JobStatus & DepSafe);
  }
}

export class JobsProcessingResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs.map(FilterByStatusMapper, "processing" as JobStatus & DepSafe);
  }
}

export class JobsCompletedResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs.map(FilterByStatusMapper, "completed" as JobStatus & DepSafe);
  }
}

export class JobsFailedResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs.map(FilterByStatusMapper, "failed" as JobStatus & DepSafe);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyJobs: Entry<JobId, JobValue>[] = Array.of();
    this.initialData = { jobs: emptyJobs };
    this.resources = { "jobs": JobsResource, "jobs-pending": JobsPendingResource, "jobs-processing": JobsProcessingResource, "jobs-completed": JobsCompletedResource, "jobs-failed": JobsFailedResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { jobs: inputs.jobs };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}

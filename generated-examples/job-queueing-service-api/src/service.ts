import type {
  EagerCollection,
  Json,
  Resource,
  ResourceClass,
  SkipService,
  Context,
  Mapper,
  Values,
  DepSafe
} from "../skipruntime/core.js";
import { InputDefinition } from "../skipruntime/core.js";

import type {
  JobId,
  JobValue,
  PendingProcessingo5ljfmEnum,
} from "./types.js";

type JobStatus = PendingProcessingo5ljfmEnum;

export type Inputs = {
  jobs: InputDefinition<JobId, JobValue>;
};

export type InputCollections = {
  jobs: EagerCollection<JobId, JobValue>;
};

export type GraphCollections = {
  jobs: EagerCollection<JobId, JobValue>;
};

export type Resources = {
  "jobs": ResourceClass<GraphCollections, {}>;
  "jobs-pending": ResourceClass<GraphCollections, {}>;
  "jobs-processing": ResourceClass<GraphCollections, {}>;
  "jobs-completed": ResourceClass<GraphCollections, {}>;
  "jobs-failed": ResourceClass<GraphCollections, {}>;
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
    const result: Array<[JobId, JobValue]> = Array.of();
    for (const v of values) {
      if (v.status === this.targetStatus) {
        result.push([key, v]);
      }
    }
    return result;
  }
}

export class JobsResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs;
  }
}

export class JobsPendingResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs.map(FilterByStatusMapper, "pending");
  }
}

export class JobsProcessingResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs.map(FilterByStatusMapper, "processing");
  }
}

export class JobsCompletedResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs.map(FilterByStatusMapper, "completed");
  }
}

export class JobsFailedResource implements Resource<GraphCollections> {
  constructor(_params: {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<JobId, JobValue> {
    return cs.jobs.map(FilterByStatusMapper, "failed");
  }
}

class Service implements SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  public inputs: Inputs;
  public resources: Resources;

  constructor() {
        this.inputs = { jobs: new InputDefinition<JobId, JobValue>([]) };
    this.resources = { "jobs": JobsResource, "jobs-pending": JobsPendingResource, "jobs-processing": JobsProcessingResource, "jobs-completed": JobsCompletedResource, "jobs-failed": JobsFailedResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { jobs: inputs.jobs };
  }
}

export function service(): SkipService<Inputs, InputCollections, GraphCollections, Resources> {
  return new Service();
}

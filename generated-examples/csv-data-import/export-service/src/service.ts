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
  CsvImportId,
  CsvImportValue,
  CsvRowId,
  CsvRowValue,
  CsvRowsByImportResourceParams,
} from "./types.js";


type Inputs = {
  csvImports: Entry<CsvImportId, CsvImportValue>[];
  csvRows: Entry<CsvRowId, CsvRowValue>[];
};

export type InputCollections = {
  csvImports: EagerCollection<CsvImportId, CsvImportValue>;
  csvRows: EagerCollection<CsvRowId, CsvRowValue>;
};

export type GraphCollections = {
  csvImports: EagerCollection<CsvImportId, CsvImportValue>;
  csvRows: EagerCollection<CsvRowId, CsvRowValue>;
};

type Resources = {
  "csvImports": new (params: Json) => Resource<GraphCollections>;
  "csvRows": new (params: Json) => Resource<GraphCollections>;
  "csvRows-byImport": new (params: Json) => Resource<GraphCollections>;
};

export class FilterRowsByImportMapper implements Mapper<CsvRowId, CsvRowValue, CsvRowId, CsvRowValue> {
  private importId: string;

  constructor(importId: string) {
    this.importId = importId;
  }

  mapEntry(
    key: CsvRowId,
    values: Values<CsvRowValue>,
    _context: Context
  ): Iterable<[CsvRowId, CsvRowValue]> {
    const result: Array<[CsvRowId, CsvRowValue]> = Array.of();
    const arr = values.toArray();
    for (let i = 0; i < arr.length; i++) {
      const v: CsvRowValue & DepSafe = arr[i]!;
      if (v.importId === this.importId) {
        result.push([key, v]);
      }
    }
    return result;
  }
}


export class CsvImportsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CsvImportId, CsvImportValue> {
    return cs.csvImports;
  }
}

export class CsvRowsResource implements Resource<GraphCollections> {
  constructor(_params: Json = {}) {
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CsvRowId, CsvRowValue> {
    return cs.csvRows;
  }
}

export class CsvRowsByImportResource implements Resource<GraphCollections> {
  private importId: string;

  constructor(params: Json) {
    const typed = params as CsvRowsByImportResourceParams;
    this.importId = typed.importId;
  }

  instantiate(
    cs: GraphCollections,
    _context: Context
  ): EagerCollection<CsvRowId, CsvRowValue> {
    return cs.csvRows.map(FilterRowsByImportMapper, this.importId);
  }
}

class Service implements SkipService<InputCollections, GraphCollections> {
  public initialData: Inputs;
  public resources: Resources;

  constructor() {
    const emptyCsvImports: Entry<CsvImportId, CsvImportValue>[] = Array.of();
    const emptyCsvRows: Entry<CsvRowId, CsvRowValue>[] = Array.of();
    this.initialData = { csvImports: emptyCsvImports, csvRows: emptyCsvRows };
    this.resources = { "csvImports": CsvImportsResource, "csvRows": CsvRowsResource, "csvRows-byImport": CsvRowsByImportResource };
  }

  createGraph(inputs: InputCollections, _context: Context): GraphCollections {
    return { csvImports: inputs.csvImports, csvRows: inputs.csvRows };
  }
}

export function service(): SkipService<InputCollections, GraphCollections> {
  return new Service();
}

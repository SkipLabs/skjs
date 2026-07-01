import type { Json } from "@skipruntime/core";

export type ApiError = { readonly code: string; readonly message: string } & {
  readonly [key: string]: Json | null;
};

export type ApiError_skip_id_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type ApiError_skip_value_ = {
  readonly code: string;
  readonly message: string;
} & { readonly [key: string]: Json | null };

export type AppendDatasetRowRequest = { readonly values: DatasetRowValues } & {
  readonly [key: string]: Json | null;
};

export type AppendDatasetRowRequest_skip_id_ = {
  readonly values: DatasetRowValues;
} & { readonly [key: string]: Json | null };

export type AppendDatasetRowRequest_skip_value_ = {
  readonly values: DatasetRowValues;
} & { readonly [key: string]: Json | null };

export type CellValue = {
  readonly booleanValue?: boolean;
  readonly dateValue?: string;
  readonly integerValue?: number;
  readonly numberValue?: number;
  readonly stringValue?: string;
  readonly type: ColumnType;
} & { readonly [key: string]: Json | null };

export type CellValue_skip_id_ = {
  readonly booleanValue?: boolean;
  readonly dateValue?: string;
  readonly integerValue?: number;
  readonly numberValue?: number;
  readonly stringValue?: string;
  readonly type: ColumnType;
} & { readonly [key: string]: Json | null };

export type CellValue_skip_value_ = {
  readonly booleanValue?: boolean;
  readonly dateValue?: string;
  readonly integerValue?: number;
  readonly numberValue?: number;
  readonly stringValue?: string;
  readonly type: ColumnType;
} & { readonly [key: string]: Json | null };

export type ColumnSpec = {
  readonly name: string;
  readonly type: ColumnType;
} & { readonly [key: string]: Json | null };

export type ColumnSpec_skip_id_ = {
  readonly name: string;
  readonly type: ColumnType;
} & { readonly [key: string]: Json | null };

export type ColumnSpec_skip_value_ = {
  readonly name: string;
  readonly type: ColumnType;
} & { readonly [key: string]: Json | null };

export type ColumnType = "STRING" | "INTEGER" | "NUMBER" | "BOOLEAN" | "DATE";

export type ColumnType_skip_id_ =
  | "STRING"
  | "INTEGER"
  | "NUMBER"
  | "BOOLEAN"
  | "DATE";

export type ColumnType_skip_value_ =
  | "STRING"
  | "INTEGER"
  | "NUMBER"
  | "BOOLEAN"
  | "DATE";

export type CreateDatasetRequest = {
  readonly columns: ColumnSpec[];
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateDatasetRequest_skip_id_ = {
  readonly columns: ColumnSpec[];
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type CreateDatasetRequest_skip_value_ = {
  readonly columns: ColumnSpec[];
  readonly description?: string;
  readonly name: string;
} & { readonly [key: string]: Json | null };

export type Dataset = {
  readonly columns: ColumnSpec[];
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly rowCount: number;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type DatasetByOwnerValue = {
  readonly columns: ColumnSpec[];
  readonly createdAt: string;
  readonly description?: string;
  readonly id: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type DatasetList = { readonly datasets: Dataset[] } & {
  readonly [key: string]: Json | null;
};

export type DatasetList_skip_id_ = { readonly datasets: Dataset[] } & {
  readonly [key: string]: Json | null;
};

export type DatasetList_skip_value_ = { readonly datasets: Dataset[] } & {
  readonly [key: string]: Json | null;
};

export type DatasetRow = {
  readonly createdAt: string;
  readonly datasetId: string;
  readonly rowIndex: number;
  readonly values: DatasetRowValues;
} & { readonly [key: string]: Json | null };

export type DatasetRowByDatasetValue = {
  readonly createdAt: string;
  readonly rowIndex: number;
  readonly values: DatasetRowValues;
} & { readonly [key: string]: Json | null };

export type DatasetRowCountAccum = number;

export type DatasetRowList = {
  readonly rows: DatasetRow[];
  readonly totalCount: number;
} & { readonly [key: string]: Json | null };

export type DatasetRowList_skip_id_ = {
  readonly rows: DatasetRow[];
  readonly totalCount: number;
} & { readonly [key: string]: Json | null };

export type DatasetRowList_skip_value_ = {
  readonly rows: DatasetRow[];
  readonly totalCount: number;
} & { readonly [key: string]: Json | null };

export type DatasetRowValues = Record<string, CellValue>;

export type DatasetRowValues_skip_id_ = Record<string, CellValue>;

export type DatasetRowValues_skip_value_ = Record<string, CellValue>;

export type DatasetRow_skip_id_ = {
  readonly datasetId: string;
  readonly rowIndex: number;
} & { readonly [key: string]: Json | null };

export type DatasetRow_skip_value_ = {
  readonly createdAt: string;
  readonly values: DatasetRowValues;
} & { readonly [key: string]: Json | null };

export type DatasetStored = {
  readonly columns: ColumnSpec[];
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type Dataset_skip_id_ = string;

export type Dataset_skip_value_ = {
  readonly columns: ColumnSpec[];
  readonly createdAt: string;
  readonly description?: string;
  readonly name: string;
  readonly ownerId: string;
  readonly rowCount: number;
  readonly updatedAt: string;
} & { readonly [key: string]: Json | null };

export type GetDatasetParams = {
  readonly datasetId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GetDatasetRowParams = {
  readonly datasetId: string;
  readonly rowIndex: number;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type GetImportJobParams = {
  readonly datasetId: string;
  readonly jobId: string;
  readonly userId: string;
} & { readonly [key: string]: Json | null };

export type ImportJob = {
  readonly createdAt: string;
  readonly datasetId: string;
  readonly errorMessage?: string;
  readonly failedRows: number;
  readonly finishedAt?: string;
  readonly id: string;
  readonly ownerId: string;
  readonly processedRows: number;
  readonly startedAt?: string;
  readonly status: ImportJobStatus;
  readonly totalRows: number;
} & { readonly [key: string]: Json | null };

export type ImportJobByDatasetValue = {
  readonly createdAt: string;
  readonly errorMessage?: string;
  readonly failedRows: number;
  readonly finishedAt?: string;
  readonly id: string;
  readonly ownerId: string;
  readonly processedRows: number;
  readonly startedAt?: string;
  readonly status: ImportJobStatus;
  readonly totalRows: number;
} & { readonly [key: string]: Json | null };

export type ImportJobList = { readonly jobs: ImportJob[] } & {
  readonly [key: string]: Json | null;
};

export type ImportJobList_skip_id_ = { readonly jobs: ImportJob[] } & {
  readonly [key: string]: Json | null;
};

export type ImportJobList_skip_value_ = { readonly jobs: ImportJob[] } & {
  readonly [key: string]: Json | null;
};

export type ImportJobStatus = "PENDING" | "RUNNING" | "SUCCEEDED" | "FAILED";

export type ImportJobStatus_skip_id_ =
  | "PENDING"
  | "RUNNING"
  | "SUCCEEDED"
  | "FAILED";

export type ImportJobStatus_skip_value_ =
  | "PENDING"
  | "RUNNING"
  | "SUCCEEDED"
  | "FAILED";

export type ImportJob_skip_id_ = string;

export type ImportJob_skip_value_ = {
  readonly createdAt: string;
  readonly datasetId: string;
  readonly errorMessage?: string;
  readonly failedRows: number;
  readonly finishedAt?: string;
  readonly ownerId: string;
  readonly processedRows: number;
  readonly startedAt?: string;
  readonly status: ImportJobStatus;
  readonly totalRows: number;
} & { readonly [key: string]: Json | null };

export type StartCsvImportRequest = { readonly csv: string } & {
  readonly [key: string]: Json | null;
};

export type StartCsvImportRequest_skip_id_ = { readonly csv: string } & {
  readonly [key: string]: Json | null;
};

export type StartCsvImportRequest_skip_value_ = { readonly csv: string } & {
  readonly [key: string]: Json | null;
};

export type UpdateDatasetRequest = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateDatasetRequest_skip_id_ = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateDatasetRequest_skip_value_ = {
  readonly description?: string;
  readonly name?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_id_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type UpdateMeRequest_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

export type User = {
  readonly displayName?: string;
  readonly email?: string;
  readonly id: string;
} & { readonly [key: string]: Json | null };

export type User_skip_id_ = string;

export type User_skip_value_ = {
  readonly displayName?: string;
  readonly email?: string;
} & { readonly [key: string]: Json | null };

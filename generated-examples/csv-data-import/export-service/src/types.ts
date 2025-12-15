export type PendingProcessingo5ljfmEnum = "completed" | "failed" | "pending" | "processing";

export type RowData = { [key: string]: string };

export type ExportRequest = {
  collectionName: string;
  filename: string | null;
};

export type ExportResult = {
  id: string;
  collectionName: string;
  filename: string;
  rowCount: number;
  csvContent: string;
  createdAt: number;
};

export type CsvImportId = string;

export type CsvImportValue = {
  filename: string;
  status: PendingProcessingo5ljfmEnum;
  rowCount: number;
  columnNames: Array<string>;
  createdAt: number;
  completedAt: number | null;
};

export type CsvImport = CsvImportValue & { id: CsvImportId };

export type CsvRowId = string;

export type CsvRowValue = {
  importId: string;
  rowNumber: number;
  data: RowData;
};

export type CsvRow = CsvRowValue & { id: CsvRowId };

export type CsvRowsByImportResourceParams = {
  importId: string;
};

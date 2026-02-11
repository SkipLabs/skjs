// File that exports a unique symbol for import testing

// Exported unique symbol works correctly
export const exportedUniqueSymbol: unique symbol = Symbol("exported");

// Regular symbol export for comparison
export const regularSymbol: symbol = Symbol("regular");

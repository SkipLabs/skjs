# skcheck

Static analyzer for Skip reactive services.

## Setup

From the skjs root:

```bash
npm install
```

## Usage

```bash
# Analyze a single project
npx skcheck --project generated-examples/todo-list-api

# Analyze all generated-examples projects
npx skcheck all

# With more parallelism
npx skcheck all --parallel 8

# Enable/disable specific checkers
npx skcheck --project generated-examples/todo-list-api --disable no-as-expression-from-json,no-as-expression-necessary,no-as-expression-unnecessary
npx skcheck --project generated-examples/todo-list-api --enable service-count,service-members

# Verbose output
npx skcheck --project generated-examples/todo-list-api --verbose

# Help
npx skcheck --help
```

## Checkers

| Checker | Description |
|---------|-------------|
| `no-as-expression-from-json` | Flags casts from `Json` type (e.g., `params as SomeType`) — prefer validated decoding |
| `no-as-expression-necessary` | Flags casts where the expression type is **not** assignable to the target type |
| `no-as-expression-unnecessary` | Flags casts where the expression type is **already** assignable to the target (can be removed) |
| `no-non-null-assertion` | Flags `!` postfix except for safe patterns (e.g., `arr[i]!` in bounded loops with guards) |
| `mapentry-values-toarray` | Ensures `Values<T>` params in `Mapper.mapEntry` are only consumed via `.toArray()` |
| `service-count` | Requires exactly one `SkipService` class per project |
| `service-members` | Validates required members (`resources`, `createGraph`) on `SkipService` |

## Code Structure

```
src/
├── infra/                    # Generic infrastructure
│   ├── ast-inspection.ts     # AST iteration and node helpers
│   ├── guard-analysis.ts     # Bound check and guard analysis
│   ├── type-analysis.ts      # Type checker utilities (assignability)
│   ├── code-frame.ts         # Error formatting with code frames
│   ├── checker.ts            # Violation type
│   └── tsc.ts                # TypeScript compiler utilities
│
├── skip/                     # Skip-specific analysis
│   ├── checkers/             # Individual checker implementations
│   │   ├── types.ts          # Checker interface
│   │   ├── index.ts          # Checker registry
│   │   └── *.ts              # Individual checkers
│   ├── collectors.ts         # AST collectors (mappers, services, map calls)
│   ├── checkers.ts           # Checker entrypoint
│   ├── report.ts             # Analysis report types
│   └── output.ts             # Output formatting
│
└── cli.ts                    # CLI entry point
```

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
npx skcheck --project generated-examples/todo-list-api --disable no-as-expression-necessary,no-as-expression-unnecessary
npx skcheck --project generated-examples/todo-list-api --enable service-count,service-members

# Verbose output
npx skcheck --project generated-examples/todo-list-api --verbose

# Help
npx skcheck --help
```

## Checkers

| Checker | Description |
|---------|-------------|
| `no-as-expression-necessary` | Forbids necessary type assertions (where the type isn't assignable without `as`) |
| `no-as-expression-unnecessary` | Forbids unnecessary type assertions (where the type is already assignable) |
| `no-non-null-assertion` | Forbids postfix `!` except for safe patterns (e.g., `arr[i]!` inside bounded loops) |
| `mapentry-values-toarray` | Ensures `Values<T>` params in `Mapper.mapEntry` are only used via `.toArray()` |
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

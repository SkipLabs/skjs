# Error Output Formats

SKJS supports multiple error output formats via `--error-format <FORMAT>`. Available formats: `default`, `indent`, `json`.

## `default`

The default human-readable format.

```text
File "path/to/file.ts", line 2, character 10-11:
Invalid return type
File "path/to/file.ts", line 1, character 16-22:
Type number
File "path/to/file.ts", line 1, character 25-31:
is not compatible with type string
```

Each error is a sequence of `<position>\n<message>` pairs. Errors are separated by a blank line.

## `indent`

Compact format with `file:line:col` positions. The first message of each error starts at the left margin; subsequent context messages are indented by 2 spaces.

```text
path/to/file.ts:2:10: Invalid return type
  path/to/file.ts:1:16: Type number
  path/to/file.ts:1:25: is not compatible with type string
```

Errors are separated by a blank line.

## `json`

Machine-readable JSON. The output is a single JSON array of error objects, pretty-printed with 2-space indentation.

### Schema

```ts
ErrorList = Array<Error>

// Non-empty array. Element 0 is the primary message; subsequent
// elements are related context (e.g., subtyping detail).
Error = Array<Message>

Message = {
  pos: Position,
  message: string
}

Position = {
  // Absolute path of the source file.
  file: string,
  // 1-based line number of the start of the range.
  line: number,
  // 1-based column number of the start of the range.
  col: number,
  // Optional. 1-based end line. Present only when different from `line`.
  endLine?: number,
  // Optional. 1-based end column. Present only when the end position
  // differs from the start position.
  endCol?: number
}
```

### Example

```json
[
  [
    {
      "pos": {
        "file": "/path/to/file.ts",
        "line": 2,
        "col": 10,
        "endCol": 11
      },
      "message": "Invalid return type"
    },
    {
      "pos": {
        "file": "/path/to/file.ts",
        "line": 1,
        "col": 16,
        "endCol": 22
      },
      "message": "Type number"
    },
    {
      "pos": {
        "file": "/path/to/file.ts",
        "line": 1,
        "col": 25,
        "endCol": 31
      },
      "message": "is not compatible with type string"
    }
  ]
]
```

### Notes

- On success (no errors), no output is produced.
- A parse error appears as an `Error` with a single `Message` (no related context).
- `endLine`/`endCol` are omitted when the range is a single point or stays on the same line.

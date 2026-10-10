# The conductor tools

The scripts that did `TODO.md` §68 phase 2 (`DONE.md` §68): turning each
front-end file of the old shape, `(define X-module (module …))` followed
by top-level re-exports, into a `load-input` file that `conductor.fx`
applies to the modules it uses, one commit a file. No file of the old
shape is left, so the converters will not run as they are. They are
kept for what they know about the files, which the passes after it
(`TODO.md` §69, §70) will need: which names come from which types file,
which module a value comes from, what each client uses of a module, and
where a file can be cut in two.

Paths come from `paths.py`: the repository is two directories up, and
what the tools write between steps goes to `target/conductor/` (or
`$CONDUCTOR_TMP`). Every long run goes through `t SECONDS COMMAND…`, which
kills the command and its children after that long.

## The pipeline, a file at a time

| Script                  | What it does                                                                                                                                                                                            |
|-------------------------|---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| `auto.py`               | `FILE:NAME:COMMENT …`: each file converted (`convert.py`) and committed (`commit.sh`), the message written from what the conversion found; stops at the first failure                                   |
| `convert.py`            | One file: rewrite it (`to_input3.py`), move it in `lib.rs` (`lib_move.py`), add it to the conductor (`conductor_add.py`, `conductor_export.py`), then the check (`fecheck.sh`), the suite and the bench |
| `to_input3.py`          | The rewrite: the `let*` of types files, the `lambda` over the modules given (each typed by its signature), the module, its imports                                                                      |
| `deps.py`               | Which front-end file defines each name a file uses                                                                                                                                                      |
| `registry2.py`          | What each types file defines (types, effects, datatype constructors) and how to load it; `registry.json` is its cache, kept by `extract.py`                                                             |
| `extract.py`, `thes.py` | Phase 1: a module's type items moved out to its `X-types.fx`                                                                                                                                            |
| `mksig.py`, `pp.py`     | A signature (`X-sig`) as the union of what clients use, from the printed types in `fe-check.txt`, laid out within 100 columns                                                                           |
| `lib_move.py`           | A file moved from the joined front end (`FRONT_END_FILES` and its groups) to the built-in modules (`FRONT_END_MODULES`) in `lib.rs`                                                                     |
| `conductor_add.py`      | The file's binding added to the front of the conductor's `let*`                                                                                                                                         |
| `conductor_export.py`   | The names Rust and `bootstrap.fx` call, named by the conductor from `front-end-entries`                                                                                                                 |
| `fecheck.sh`            | Rebuild, then check the whole front end in both checkers; prints the verdict                                                                                                                            |
| `commit.sh`             | Commit the sources, tests and `TODO.md`, with the fresh bench tables and an optional `trailer.txt`                                                                                                      |

## Splitting a file that would pass 1000 lines

| Script       | What it does                                                                                              |
|--------------|-----------------------------------------------------------------------------------------------------------|
| `seams.py`   | Where a module's items can be cut in two: every item before the cut uses nothing after it                 |
| `leaves.py`  | For a file that is one recursive knot (no seams): the items that use nothing of the knot                  |
| `reorder.py` | Those leaves moved to the front, in their order, each with its comments: the same lines, reordered        |
| `split.py`   | The items before a cut moved by extraction to a new file made before it, the clients given the new module |

## One-offs

| Script           | What it did                                                                   |
|------------------|-------------------------------------------------------------------------------|
| `trim_reader.py` | Dropped the re-exports of `reader.fx` that nothing names (`--write` to write) |
| `arrays.py`      | Checks that each `[(&str, &str); N]` array in `lib.rs` has `N` entries        |

## What went wrong, so that the next pass looks for it

- A build failure runs no tests and so prints no `FAILED`: the suite step
  counts the results that pass too, and fails below 100.
- `mksig.py` once took the value name in `(val k-trail …)` for a use of the
  type `k-trail`, loading a types file that closed a load cycle; the Rust
  checker hung on it (`TODO.md` §71). It now skips value names.
- A converted file's closers on its last line can pass 100 columns; they
  go on a line of their own then.
- `split.py` once ended the moved part at the comments before the cut,
  commenting out its closers; it now ends at the last item moved.

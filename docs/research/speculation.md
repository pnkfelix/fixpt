# Speculation: a check that leaves nothing behind

The checker is often asked about a form it must then forget:

- the REPL checks what is typed, at each key, to say what is wrong or what
  comes next (`Checker::try_top`, `scratch`), and then forgets the symbols
  it read (`Interner::truncate`, by the line editor);
- a form the checker refuses must leave the session as it was, so that it
  can be typed again, corrected or not, and checked the same way
  (`Checker::top_defining`);
- the REPL's hints (`describe_argument`) and a redefinition's trial
  (`try_defining`) check and forget too.

A check changes more than the environment. As it goes it learns things it
keeps for the rest of the program: each file `load-module` loads, once
(`shared_loads`), and its hidden global's definition; generative types;
the variable each `(select m e)` effect stands for; conversions, lemmas,
facts proved. Each of these is keyed by, or holds, ids of the arena (types,
variables, expressions), which `scratch` resets: a table that keeps an id
past the reset names something gone, or, once the id is made again,
something else entirely.

## The rule

What a check thrown away or refused changed is put back: `Checker::keep`
saves, and `put_back` restores,

- the lengths of every table that grows as the checker learns, cut back;
- every set or map keyed by, or holding, an id made since the arena's mark,
  those entries dropped;
- the loads made for the first time, and their definitions;
- the state set around what is being checked (the hidden scope, the depth
  of `include`s and `with`s, the call being checked), which a refusal can
  leave set.

`scratch` also resets the arena and forgets the facts recorded since; a
refused check leaves its ids in the arena unused.

## Enforced

`every_field_placed` (`top.rs`) destructures the checker with no `..`: a
field added does not compile until it is placed, as put back, as the
environment's, as the arena's, as set and restored around one operation, or
as a setting no check changes.

## Found by

- 2026-10-27: `(load-module "f")` typed at the REPL panicked, the load
  recorded under a symbol the interner had forgotten (`ae7d7670`).
- 2026-10-27: a module refused for making state, typed again, was taken
  the second time as though the files it loaded had been made; typed at a
  terminal, where it was first checked as it was typed, the variable for
  `(select core cmd-eff)` named another (`a s is expected here, and this is
  a s'`).

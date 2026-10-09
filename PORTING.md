# Porting log

Every definition or proof taken from another project is recorded here: source
repository, commit, paths, license and the changes made. Ported proofs are
re-checked by this project's build.

## Dependencies

| Dependency | Where | Pinned commit | Use |
|---|---|---|---|
| [strictness-pcf](https://github.com/clayrat/strictness-pcf) | `vendor/strictness-pcf` (git submodule) | `67d26ac` | Source PCF: `Ty`, `Syntax`, `Context`, `Typing`, `Checker`, `Subst`, `OperationalSemantics`, `Safety` and `Examples` (for `add`, `mul`, `fact`, `omega_at`), built under the prefix `PCF`; the strictness analyser and its Tests.v are not built. The submodule is not edited; adapters live in `theories/PCFTranslation/`. |

## Ported files

| Here | Source | Commit | License | Changes |
|---|---|---|---|---|
| `theories/Common/Result.v` | modules-system-fw, `theories/Fw/Result.v` | `5a24fa7` | no license file | header comment only |
| `theories/Common/Traced.v` | modules-system-fw, `theories/Fw/Traced.v` | `5a24fa7` | no license file | dropped the unused import of `Fw.Syntax`; header comment |

## Adapted proofs and code

| Here | Source | Commit | Changes |
|---|---|---|---|
| `omega_at_loop`, `omega_at_diverges` in `theories/PCFTranslation/Programs.v` | strictness-pcf, `theories/Tests.v` | `67d26ac` | re-proved with the same proofs, since Tests.v needs the strictness analyser and Equations |
| `diverges_pred1` in `theories/PCFTranslation/Programs.v` | strictness-pcf, `diverges_succ1` in `theories/OperationalSemantics.v` | `67d26ac` | the same proof through the rule `S_Pred1`; strictness-pcf has no lemma for `pred` |
| `extraction/` (Makefile, dune, `Extract.v`, the shape of `pretty.ml`, `main.ml`, `regress.ml`) | modules-system-fw, `extraction/` | `5a24fa7` | the scheme of extraction, printing and demos; written anew for the PTS syntax, with `fresh` in `pretty.ml` following its namesake |
| `reference/` (native OCaml reference and differential test) | strictness-pcf `reference/pcf_native.ml`, modules-system-fw `reference/` | `67d26ac`, `5a24fa7` | the arrangement of a standalone native version compared with the extract; the code is new |

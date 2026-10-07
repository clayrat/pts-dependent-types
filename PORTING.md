# Porting log

Every definition or proof taken from another project is recorded here: source
repository, commit, paths, license and the changes made. Ported proofs are
re-checked by this project's build.

## Dependencies

| Dependency | Where | Pinned commit | Use |
|---|---|---|---|
| [strictness-pcf](https://github.com/clayrat/strictness-pcf) | `vendor/strictness-pcf` (git submodule) | `67d26ac` | Source PCF: `Ty`, `Syntax`, `Context`, `Typing`, `Checker`, `Subst`, `OperationalSemantics`, `Safety`, built under the prefix `PCF`. The submodule is not edited; adapters live in `theories/PCFTranslation/`. |

## Ported files

| Here | Source | Commit | License | Changes |
|---|---|---|---|---|
| `theories/Common/Result.v` | modules-system-fw, `theories/Fw/Result.v` | `5a24fa7` | no license file | header comment only |
| `theories/Common/Traced.v` | modules-system-fw, `theories/Fw/Traced.v` | `5a24fa7` | no license file | dropped the unused import of `Fw.Syntax`; header comment |

import Lake
import Lake.Build.Module

open Lake DSL

package «sha256-bridge» where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, .ofBool false⟩,
    ⟨`relaxedAutoImplicit, .ofBool false⟩,
    ⟨`warningAsError, .ofBool true⟩]

require LeanSha256 from git "https://github.com/etheorem/LeanSha256" @
  "f3432475b3233b259b65443da762bb590bcf8398"
require hash from git "https://github.com/pure-algebra/lean4-hash" @
  "ab7eda433f0390fde7aa240189761540c9744c79"

@[default_target]
lean_lib Sha256Bridge where
  globs := #[.one `Sha256Bridge, .submodules `Sha256Bridge]

@[default_target]
lean_exe «sha256-bridge-vectors» where
  root := `Sha256Bridge.Runner

-- Ticket #26, coordinator ruling #2: the pinned Hash.Sha256 modules predate
-- Lean 4.34.1's if_pos/dif_pos/dif_neg renames. Change only their in-memory
-- options; delegate all build work to Lake's standard presetup facet.
-- Package + namespace checks exclude Hash.Sha3, LeanSha256, and our own code.
@[«module_facet»] def sha256Presetup : ModuleFacetDecl :=
  ⟨Module.presetupFacet, mkFacetJobConfig (buildable := false) fun mod => do
    let mod := if mod.pkg.baseName == `hash && (`Hash.Sha256).isPrefixOf mod.name then
      { mod with lib := { mod.lib with config :=
          { mod.lib.config with leanOptions :=
              mod.lib.config.leanOptions.push ⟨`warningAsError, .ofBool false⟩ } } }
      else mod
    Module.presetupFacetConfig.run mod⟩

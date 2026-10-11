/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.EtaleIrreducibleComponents
import Mathlib.Topology.Connected.Clopen

/-!
# Connected schemes with domain stalks

On a locally Noetherian scheme with domain stalks, irreducible components are
open and closed. Connectedness therefore forces one component to be the whole
scheme, and reducedness follows directly from the stalks.
-/

noncomputable section

open TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- A connected locally Noetherian scheme whose stalks are domains is integral. -/
theorem isIntegral_of_connected_of_isDomain_stalk
    (X : Scheme.{u}) [IsLocallyNoetherian X] [ConnectedSpace X]
    (hdom : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsIntegral X := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let Z : Set X := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hclopen : IsClopen Z :=
    ⟨isClosed_of_mem_irreducibleComponents Z hZ,
      Scheme.isOpen_irreducibleComponent_of_isDomain_stalk X hdom Z hZ⟩
  have hZuniv : Z = Set.univ := hclopen.eq_univ hZ.1.1
  let : IrreducibleSpace X :=
    { isPreirreducible_univ := hZuniv ▸ hZ.1.2, toNonempty := ⟨x⟩ }
  let (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    let : IsDomain (X.presheaf.stalk x) := hdom x
    infer_instance
  let : IsReduced X := isReduced_of_isReduced_stalk X
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end AlgebraicGeometry

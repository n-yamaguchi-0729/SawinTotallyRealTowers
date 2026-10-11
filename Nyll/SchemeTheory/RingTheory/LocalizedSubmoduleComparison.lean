/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Full localized submodules in the actual localization module

If a submodule becomes the whole canonical localized module, it also
becomes the whole of any actual localization. The proof transfers actual
fraction representatives along the localized identity map. This is the
comparison needed to use finite-generator extraction for sheaf sections.
-/

noncomputable section

universe u v w

namespace Submodule

/-- Fullness of the canonical localized submodule gives fullness in the
actual localized module, with its supplied localization map. -/
theorem localized₀_eq_top_of_localized_eq_top
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (S : Submonoid R) (K : Submodule R M) (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (hK : K.localized S = ⊤) : K.localized₀ S f = ⊤ := by
  let q : LocalizedModule S M →ₗ[R] N :=
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M) f (LinearMap.id (R := R))
  have hq : Function.Surjective q :=
    IsLocalizedModule.map_surjective S (LocalizedModule.mkLinearMap S M) f
      (LinearMap.id (R := R)) Function.surjective_id
  apply top_unique
  intro x _
  obtain ⟨z, rfl⟩ := hq x
  have hz : z ∈ K.localized S := by
    rw [hK]
    exact trivial
  obtain ⟨m, hm, d, hd⟩ :=
    (Submodule.mem_localized' (Localization S) S
      (LocalizedModule.mkLinearMap S M) K z).mp hz
  apply (Submodule.mem_localized₀ S f K (q z)).mpr
  refine ⟨m, hm, d, ?_⟩
  calc
    IsLocalizedModule.mk' f m d =
        q (IsLocalizedModule.mk' (LocalizedModule.mkLinearMap S M) m d) :=
      (IsLocalizedModule.map_mk' S (LocalizedModule.mkLinearMap S M) f
        (LinearMap.id (R := R)) m d).symm
    _ = q z := congrArg q hd

end Submodule

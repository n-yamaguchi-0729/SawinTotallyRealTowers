/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.StandardClasses

/-!
# Inclusion of finite Sigma-group classes

Enlarging the permitted primes preserves the actual prime-divisor condition.
No nonemptiness or primality assumption on the containing sets is needed.
-/

namespace ProCGroups.FiniteGroupClass

universe u

/-- A Sigma-number remains admissible when the set of permitted primes grows. -/
theorem IsSigmaNumber.mono {sigma tau : Set ℕ} {n : ℕ}
    (h : sigma ⊆ tau) (hn : IsSigmaNumber sigma n) :
    IsSigmaNumber tau n := by
  intro p hp hptau hpn
  exact hn p hp (fun hpsigma => hptau (h hpsigma)) hpn

/-- Inclusion of sets of primes gives inclusion of the corresponding finite-group classes. -/
theorem sigmaGroup_mono {sigma tau : Set ℕ} (h : sigma ⊆ tau)
    {G : Type u} [Group G] (hG : sigmaGroup sigma G) : sigmaGroup tau G := by
  exact ⟨hG.1, IsSigmaNumber.mono h hG.2⟩

end ProCGroups.FiniteGroupClass

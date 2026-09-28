import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedDiamondReflection

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn

def signedCoordinateCut (sign : Bool) (x : ℝ) : Prop := if sign then 0 ≤ x else x ≤ 0

def signedCoordinateSector {E : Type*} (D : Set E) (c : Fin 2 → E → ℝ)
    (eta : Fin 2 → Bool) (eps delta : Bool) : Set E :=
  {z | z ∈ D ∧ signedCoordinateCut (signedTubeReindex (eta 0) eps) (c 0 z) ∧
    signedCoordinateCut (signedTubeReindex (eta 1) delta) (c 1 z)}

def signedCoordinateFace {E : Type*} (D : Set E) (c : Fin 2 → E → ℝ)
    (eta : Fin 2 → Bool) (i : Fin 2) (sign : Bool) : Set E :=
  {z | z ∈ D ∧ c i z = 0 ∧ signedCoordinateCut (signedTubeReindex (eta i.rev) sign) (c i.rev z)}

theorem signedCoordinateCut_opposite (keep sign : Bool) (x : ℝ) :
    signedCoordinateCut (signedTubeReindex keep sign) x ∧
      signedCoordinateCut (signedTubeReindex keep (!sign)) x ↔ x = 0 := by
  cases keep <;> cases sign <;>
    simp only [signedTubeReindex, signedCoordinateCut, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, if_false, if_true] <;>
    constructor
  all_goals intro h
  all_goals first
    | exact le_antisymm h.1 h.2
    | exact le_antisymm h.2 h.1
    | exact h ▸ ⟨le_rfl, le_rfl⟩

theorem signedCoordinateSector_incidence {E : Type*} (D : Set E)
    (c : Fin 2 → E → ℝ) (eta : Fin 2 → Bool) (eps delta : Bool) :
    signedCoordinateSector D c eta eps delta ∩ signedCoordinateSector D c eta eps (!delta) =
      signedCoordinateFace D c eta 1 eps ∧
    signedCoordinateSector D c eta eps delta ∩ signedCoordinateSector D c eta (!eps) delta =
      signedCoordinateFace D c eta 0 delta ∧
    signedCoordinateSector D c eta eps delta ∩ signedCoordinateSector D c eta (!eps) (!delta) =
      {z | z ∈ D ∧ c 0 z = 0 ∧ c 1 z = 0} ∧
    signedCoordinateFace D c eta 0 delta ∩ signedCoordinateFace D c eta 1 eps =
      {z | z ∈ D ∧ c 0 z = 0 ∧ c 1 z = 0} := by
  have hz (sign : Bool) : signedCoordinateCut sign 0 := by cases sign <;> exact le_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext z
    have ho := signedCoordinateCut_opposite (eta 1) delta (c 1 z)
    change (z ∈ D ∧ signedCoordinateCut (signedTubeReindex (eta 0) eps) (c 0 z) ∧
        signedCoordinateCut (signedTubeReindex (eta 1) delta) (c 1 z)) ∧
      (z ∈ D ∧ signedCoordinateCut (signedTubeReindex (eta 0) eps) (c 0 z) ∧
        signedCoordinateCut (signedTubeReindex (eta 1) (!delta)) (c 1 z)) ↔
      z ∈ D ∧ c 1 z = 0 ∧ signedCoordinateCut (signedTubeReindex (eta 0) eps) (c 0 z)
    tauto
  · ext z
    have ho := signedCoordinateCut_opposite (eta 0) eps (c 0 z)
    change (z ∈ D ∧ signedCoordinateCut (signedTubeReindex (eta 0) eps) (c 0 z) ∧
        signedCoordinateCut (signedTubeReindex (eta 1) delta) (c 1 z)) ∧
      (z ∈ D ∧ signedCoordinateCut (signedTubeReindex (eta 0) (!eps)) (c 0 z) ∧
        signedCoordinateCut (signedTubeReindex (eta 1) delta) (c 1 z)) ↔
      z ∈ D ∧ c 0 z = 0 ∧ signedCoordinateCut (signedTubeReindex (eta 1) delta) (c 1 z)
    tauto
  · ext z
    have h0 := signedCoordinateCut_opposite (eta 0) eps (c 0 z)
    have h1 := signedCoordinateCut_opposite (eta 1) delta (c 1 z)
    simp only [signedCoordinateSector, mem_inter_iff, mem_setOf_eq]
    tauto
  · ext z
    change ((z ∈ D ∧ c 0 z = 0 ∧ signedCoordinateCut (signedTubeReindex (eta 1) delta) (c 1 z)) ∧
      (z ∈ D ∧ c 1 z = 0 ∧ signedCoordinateCut (signedTubeReindex (eta 0) eps) (c 0 z))) ↔
      z ∈ D ∧ c 0 z = 0 ∧ c 1 z = 0
    constructor
    · exact fun h => ⟨h.1.1, h.1.2.1, h.2.2.1⟩
    · rintro ⟨hd, h0, h1⟩
      exact ⟨⟨hd, h0, h1 ▸ hz _⟩, hd, h1, h0 ▸ hz _⟩

theorem signedCoordinateSector_cover {E : Type*} (D : Set E)
    (c : Fin 2 → E → ℝ) (eta : Fin 2 → Bool) :
    (⋃ eps, ⋃ delta, signedCoordinateSector D c eta eps delta) = D := by
  classical
  ext z
  constructor
  · rintro ⟨_, ⟨eps, rfl⟩, _, ⟨delta, rfl⟩, hz⟩
    exact hz.1
  · intro hz
    have hsign (i : Fin 2) : ∃ sign : Bool, signedCoordinateCut sign (c i z) := by
      by_cases h : 0 ≤ c i z
      · exact ⟨true, h⟩
      · exact ⟨false, (lt_of_not_ge h).le⟩
    obtain ⟨eps, heps⟩ := hsign 0
    obtain ⟨delta, hdelta⟩ := hsign 1
    refine mem_iUnion.mpr ⟨signedTubeReindex (eta 0) eps,
      mem_iUnion.mpr ⟨signedTubeReindex (eta 1) delta, hz, ?_, ?_⟩⟩
    · simpa only [signedTubeReindex_involutive] using heps
    · simpa only [signedTubeReindex_involutive] using hdelta

end PoincareConjecture.M76.Dehn

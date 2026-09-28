import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCenteredCylinderJets
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderPullbackSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

theorem exists_endTail_reference_index (N : ℕ) {s : ℝ} (hs : (N : ℝ) + 9 / 2 < s) :
    ∃ k : ℕ, N ≤ k ∧ s - (k + 1 : ℕ) ∈ Icc (17 / 5 : ℝ) (23 / 5) := by
  let k : ℕ := ⌊s - 9 / 2⌋₊
  have hs0 : 0 ≤ s - 9 / 2 := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hk : N ≤ k := (Nat.le_floor_iff hs0).mpr (by linarith)
  have hlo := Nat.floor_le hs0
  have hhi := Nat.lt_floor_add_one (s - 9 / 2)
  refine ⟨k, hk, ?_⟩
  change (17 / 5 : ℝ) ≤ s - (k + 1 : ℕ) ∧ s - (k + 1 : ℕ) ≤ 23 / 5
  simp only [Nat.cast_add, Nat.cast_one]
  dsimp [k]
  constructor <;> linarith

theorem endCenteredCylinder_familyClose_of_tail
    {g0 : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g0)
    (G : ℝ → RiemannianMetric 3 StandardCapSpace) (I : Set ℝ)
    {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (htail : ∀ k ≥ N, ∀ t ∈ I, ∀ q : UnitTwoSphere,
      ∀ r ∈ Icc (17 / 5 : ℝ) (23 / 5),
        roundCylinderJetErrorSquared t
          (roundCylinderPullback (G t) (endAxialTranslation e (k + 1 : ℕ) ∘ e.coordinate))
          ⌊ε⁻¹⌋₊ (q, r) ≤ ε ^ 2 / 4)
    {H : ℝ} (hH : (N : ℝ) + 9 / 2 < H - ε⁻¹) :
    RoundCylinderFamilyClose ε I
      (fun t => roundCylinderPullback (G t) (endCenteredCylinderMap e H)) := by
  have hHL : ε⁻¹ < H := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  refine ⟨?_, ε ^ 2 / 4, by nlinarith [sq_pos_of_pos hε], ?_⟩
  · intro t _
    apply roundCylinderTensorSmoothOn_pullback (G t)
    intro z hz
    exact (endCenteredCylinderMap_contMDiffAt e H (by linarith [hz.2.1])).contMDiffWithinAt
  · intro t ht z hz
    obtain ⟨k, hk, hr⟩ := exists_endTail_reference_index N
      (s := H + z.2) (by linarith [hz.1])
    have hpos : 0 < z.2 + (H - (k + 1 : ℕ)) := by linarith [hr.1]
    rw [endCenteredCylinderJetErrorSquared_eq e (k + 1) H (G t) t ⌊ε⁻¹⌋₊ hpos]
    have hpoint : cylinderAxialTranslation (H - (k + 1 : ℕ)) z =
        (z.1, H + z.2 - (k + 1 : ℕ)) := by
      apply Prod.ext
      · rfl
      · dsimp [cylinderAxialTranslation]
        ring
    rw [hpoint]
    exact htail k hk t ht z.1 _ hr

end PoincareConjecture.M34

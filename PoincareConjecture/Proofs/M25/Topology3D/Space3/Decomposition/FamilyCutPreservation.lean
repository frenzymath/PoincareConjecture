import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.FamilyLevelDeletion
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Decomposition.RetainedCapPlacement










set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


theorem family_levels_preserved_at_separated_cut
    (old new : Set E3) (u : UnitTwoSphere)
    (t s d eps w : ℝ)
    (hwidth : w ≤ d) (heps : eps ≤ d)
    (hseparated : Disjoint (Icc (t - d) (t + d))
      (Icc (s - d) (s + d)))
    (houter : ∀ y : E3, w ≤ |⟪(u : E3), y⟫_ℝ - t| →
      (y ∈ new ↔ y ∈ old))
    (m : ℕ) (B : Fin m → BallNeighborhoodChart E2 E2)
    (Phi : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hlevel : ∀ z ∈ Ioo (s - eps) (s + eps), ∀ p : E2,
      (heightPlaneCoordinates u).symm (Phi z p, z) ∈ old ↔
        p ∈ (⋃ i : Fin m, (B i).boundary)) :
    ∀ z ∈ Ioo (s - eps) (s + eps), ∀ p : E2,
      (heightPlaneCoordinates u).symm (Phi z p, z) ∈ new ↔
        p ∈ (⋃ i : Fin m, (B i).boundary) := by
  intro z hz p
  have hzs : z ∈ Icc (s - d) (s + d) :=
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hzt : d < |z - t| := by
    by_contra h
    obtain ⟨hlo, hhi⟩ := abs_le.mp (le_of_not_gt h)
    exact disjoint_left.mp hseparated
      ⟨by linarith, by linarith⟩ hzs
  let y := (heightPlaneCoordinates u).symm (Phi z p, z)
  have hyz : ⟪(u : E3), y⟫_ℝ = z := by
    dsimp only [y]
    rw [← heightPlaneCoordinates_snd, ContinuousLinearEquiv.apply_symm_apply]
  have hwy : w ≤ |⟪(u : E3), y⟫_ℝ - t| := by
    rw [hyz]
    exact hwidth.trans hzt.le
  exact (houter y hwy).trans (hlevel z hz p)


theorem SurgeryCapTag.cap_outside_other_cut_buffer
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u)
    (r : ℕ) (cut : Fin r → ℝ) (d : ℝ)
    (hseparated : Pairwise (fun a b : Fin r =>
      Disjoint (Icc (cut a - d) (cut a + d))
        (Icc (cut b - d) (cut b + d))))
    (j : Fin r) (hcut : C.cutHeight = cut j)
    (hremoval : C.removal ≤ d)
    (a : Fin r) (hne : a ≠ j) :
    ∀ y ∈ C.cap, d < |⟪(u : E3), y⟫_ℝ - cut a| := by
  intro y hy
  have hbound : |⟪(u : E3), y⟫_ℝ - cut j| ≤ d := by
    rw [← hcut]
    exact (C.cap_abs_height_bounds y hy).2.trans hremoval
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbound
  have hj : ⟪(u : E3), y⟫_ℝ ∈ Icc (cut j - d) (cut j + d) :=
    ⟨by linarith, by linarith⟩
  by_contra h
  obtain ⟨hao, hai⟩ := abs_le.mp (le_of_not_gt h)
  have ha : ⟪(u : E3), y⟫_ℝ ∈ Icc (cut a - d) (cut a + d) :=
    ⟨by linarith, by linarith⟩
  exact disjoint_left.mp (hseparated hne) ha hj

end PoincareConjecture.M25.Topology3D

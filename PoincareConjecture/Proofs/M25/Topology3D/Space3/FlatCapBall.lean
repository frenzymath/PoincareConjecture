import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FlatCapModel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightCoordinates












set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_flatCapBallChart
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2) × ℝ) F)
    (hsource : closedBall 0 1 ×ˢ (univ : Set ℝ) ⊆ e.source)
    (he : ContDiffOn ℝ ∞ e e.source)
    (hi : ContDiffOn ℝ ∞ e.symm e.target) :
    ∃ B : BallNeighborhoodChart (EuclideanSpace ℝ (Fin 3)) F,
      (∀ (x : EuclideanSpace ℝ (Fin 2)), ‖x‖ ≤ 1 / 4 →
        ∀ eps : ℝ, |eps| = 1 →
        B.chart (heightCoordinates.symm (x, eps * Real.sqrt (1 - ‖x‖ ^ 2))) = e (x, eps)) ∧
      (∀ (q : EuclideanSpace ℝ (Fin 2)), ‖q‖ = 1 →
        ∀ z : ℝ, |z| ≤ 1 / 4 →
        B.chart (heightCoordinates.symm (Real.sqrt (1 - z ^ 2) • q, z)) = e (q, z)) := by
  obtain ⟨a, ha, ha1, hanear, hafar, habound⟩ := exists_bounded_flatCap_profile (E := ℝ)
  obtain ⟨b, hb, hbpos, hbnear, hbfar⟩ :=
    exists_flatCap_profile (E := EuclideanSpace ℝ (Fin 2))
  have hapos (z : ℝ) : 0 < a z := zero_lt_one.trans_le (ha1 z)
  have ha0 (z : ℝ) : a z ≠ 0 := (hapos z).ne'
  have hb0 (x : EuclideanSpace ℝ (Fin 2)) : b x ≠ 0 := (hbpos x).ne'
  have hafar' (z : ℝ) (hz : 1 / 2 ≤ |z|) : a z = 1 := by
    exact hafar z (by simpa only [Real.norm_eq_abs] using hz)
  have hanear' (z : ℝ) (hz : |z| ≤ 1 / 4) :
      a z = (Real.sqrt (1 - z ^ 2))⁻¹ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      hanear z (by simpa only [Real.norm_eq_abs] using hz)
  have habound' (z : ℝ) (hz : |z| < 1) :
      a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      habound z (by simpa only [Real.norm_eq_abs] using hz)
  let D := heightCoordinates.toDiffeomorph.trans (flatCapDiffeomorph a b ha hb ha0 hb0)
  let B : BallNeighborhoodChart (EuclideanSpace ℝ (Fin 3)) F := {
    chart := D.toHomeomorph.toOpenPartialHomeomorph.trans e
    closedBall_subset_source := by
      intro x hx
      refine ⟨mem_univ x, hsource ⟨?_, mem_univ _⟩⟩
      apply mem_closedBall_zero_iff.mpr
      change ‖(flatCapDiffeomorph a b ha hb ha0 hb0 (heightCoordinates x)).1‖ ≤ 1
      apply flatCapDiffeomorph_fst_norm_le a b ha hb ha0 hb0 hapos habound'
      rw [← heightCoordinates_norm_sq]
      have hx' := mem_closedBall_zero_iff.mp hx
      nlinarith [norm_nonneg x]
    smooth := he.comp D.contMDiff_toFun.contDiff.contDiffOn (fun _ hx => hx.2)
    smooth_symm := D.contMDiff_invFun.contDiff.comp_contDiffOn
      (hi.mono (fun _ hy => hy.1)) }
  refine ⟨B, ?_, ?_⟩
  · intro x hx eps heps
    change e (flatCapDiffeomorph a b ha hb ha0 hb0
      (heightCoordinates (heightCoordinates.symm
        (x, eps * Real.sqrt (1 - ‖x‖ ^ 2))))) = e (x, eps)
    rw [heightCoordinates.apply_symm_apply,
      flatCapDiffeomorph_cap a b ha hb ha0 hb0 hafar' hbnear x hx eps heps]
  · intro q hq z hz
    change e (flatCapDiffeomorph a b ha hb ha0 hb0
      (heightCoordinates (heightCoordinates.symm
        (Real.sqrt (1 - z ^ 2) • q, z)))) = e (q, z)
    rw [heightCoordinates.apply_symm_apply,
      flatCapDiffeomorph_cylinder a b ha hb ha0 hb0 hanear' hbfar q hq z hz]

end PoincareConjecture.M25.Topology3D

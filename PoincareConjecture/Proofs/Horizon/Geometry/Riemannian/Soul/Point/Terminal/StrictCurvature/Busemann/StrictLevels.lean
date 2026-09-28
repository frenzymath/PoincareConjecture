import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Horoball
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

theorem exists_smaller_horoball_level_of_transformed_gap
    {p x : M} {c δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ ray : ℝ → M, IsRay ray → ray 0 = p →
      1 - Real.exp c + δ ≤ 1 - Real.exp (-busemann ray x)) :
    ∃ ε : ℝ, 0 < ε ∧ x ∈ horoballIntersection p (c - ε) := by
  have hcont : Continuous (fun t : ℝ => 1 - Real.exp (c - t)) := by fun_prop
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),
      1 - Real.exp (c - t) < 1 - Real.exp c + δ := by
    exact (hcont.continuousAt (x := 0)).eventually_lt_const
      (by simpa only [sub_zero] using lt_add_of_pos_right (1 - Real.exp c) hδ)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hhalf : dist (r / 2) 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
    linarith
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro ray hray hray0
  have h := (hball hhalf).trans_le (hgap ray hray hray0)
  have hexp : Real.exp (-busemann ray x) < Real.exp (c - r / 2) := by linarith
  have harg := Real.exp_lt_exp.mp hexp
  linarith

theorem midpoint_mem_interior_horoball_of_uniform_transformed_concavity
    {p : M} {curve : ℝ → M} {a b c δ : ℝ} (hab : a < b) (hδ : 0 < δ)
    (ha : curve a ∈ horoballIntersection p c)
    (hb : curve b ∈ horoballIntersection p c)
    (hconc : ∀ ray : ℝ → M, IsRay ray → ray 0 = p →
      ConcaveOn ℝ (Icc a b)
        (fun t => 1 - Real.exp (-busemann ray (curve t)) + δ * t ^ 2)) :
    curve ((a + b) / 2) ∈ interior (horoballIntersection p c) := by
  have hgap : 0 < δ * (b - a) ^ 2 / 4 := by positivity
  have hbound : ∀ ray : ℝ → M, IsRay ray → ray 0 = p →
      1 - Real.exp c + δ * (b - a) ^ 2 / 4 ≤
        1 - Real.exp (-busemann ray (curve ((a + b) / 2))) := by
    intro ray hray hray0
    have hca := ha ray hray hray0
    have hcb := hb ray hray hray0
    have hexpa : Real.exp (-busemann ray (curve a)) ≤ Real.exp c :=
      Real.exp_le_exp.mpr (by linarith)
    have hexpb : Real.exp (-busemann ray (curve b)) ≤ Real.exp c :=
      Real.exp_le_exp.mpr (by linarith)
    have hJ := (hconc ray hray hray0).2
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
      (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    simp only [smul_eq_mul] at hJ
    rw [show (1 / 2 : ℝ) * a + (1 / 2 : ℝ) * b = (a + b) / 2 by ring] at hJ
    nlinarith only [hJ, hexpa, hexpb]
  obtain ⟨ε, hε, hsmall⟩ := exists_smaller_horoball_level_of_transformed_gap hgap hbound
  exact horoballIntersection_subset_interior p (sub_lt_self c hε) hsmall

end Poincare.Riemannian.Soul

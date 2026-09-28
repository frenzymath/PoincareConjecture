import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.VolumeSupport
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap









set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.SurfaceEntropy

noncomputable def relativeDensity (r x : ℝ) : ℝ := x * Real.log (x / r) - x + r

theorem relativeDensity_pos {r x : ℝ} (hr : 0 < r) (hx : 0 < x)
    (hne : x ≠ r) : 0 < relativeDensity r x := by
  have hneq : r / x ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq (ne_of_gt hx)).mp h).symm
  have h := mul_lt_mul_of_pos_left
    (Real.log_lt_sub_one_of_pos (div_pos hr hx) hneq) hx
  rw [Real.log_div (ne_of_gt hr) (ne_of_gt hx)] at h
  have heq : x * (r / x - 1) = r - x := by field_simp
  rw [heq] at h
  unfold relativeDensity
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hr)]
  nlinarith

theorem relativeDensity_nonneg {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    0 ≤ relativeDensity r x := by
  by_cases h : x = r
  · subst x
    simp [relativeDensity, ne_of_gt hr]
  · exact (relativeDensity_pos hr hx h).le

theorem relativeDensity_eq_zero_iff {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    relativeDensity r x = 0 ↔ x = r := by
  constructor
  · intro h
    by_contra hne
    exact (ne_of_gt (relativeDensity_pos hr hx hne)) h
  · rintro rfl
    simp [relativeDensity, ne_of_gt hr]

theorem continuous_relativeDensity {X : Type*} [TopologicalSpace X]
    {R : X → ℝ} (hR : Continuous R) {r : ℝ} (hr : 0 < r)
    (hpos : ∀ x, 0 < R x) : Continuous (fun x => relativeDensity r (R x)) :=
  ((hR.mul ((hR.div_const r).log (fun x => ne_of_gt (div_pos (hpos x) hr)))).sub hR).add
    continuous_const

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
  [BorelSpace M] [T3Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [CompactSpace M] in
theorem integral_relativeDensity_nonneg (g : RiemannianMetric n M)
    {R : M → ℝ} {r : ℝ} (hr : 0 < r) (hpos : ∀ x, 0 < R x) :
    0 ≤ ∫ x, relativeDensity r (R x) ∂g.volumeMeasure :=
  integral_nonneg (fun x => relativeDensity_nonneg hr (hpos x))

theorem integral_relativeDensity_eq_zero_iff (g : RiemannianMetric n M)
    {R : M → ℝ} (hR : Continuous R) {r : ℝ} (hr : 0 < r)
    (hpos : ∀ x, 0 < R x) :
    (∫ x, relativeDensity r (R x) ∂g.volumeMeasure) = 0 ↔ ∀ x, R x = r := by
  let : g.volumeMeasure.IsOpenPosMeasure := g.volumeMeasure_isOpenPosMeasure
  have hc := continuous_relativeDensity hR hr hpos
  have hi := hc.integrable_of_hasCompactSupport (μ := g.volumeMeasure)
    (HasCompactSupport.of_compactSpace _)
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg
      (fun x => relativeDensity_nonneg hr (hpos x)) hi).mp h
    have heq := Measure.eq_of_ae_eq hae hc continuous_const
    intro x
    exact (relativeDensity_eq_zero_iff hr (hpos x)).mp (congrFun heq x)
  · intro h
    simp only [show (fun x => relativeDensity r (R x)) = fun _ => 0 from funext
      (fun x => (relativeDensity_eq_zero_iff hr (hpos x)).mpr (h x)), integral_zero]

end PoincareConjecture.SurfaceEntropy

import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.CylinderMetric
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Uniformization.Scalar.RegularizedArea
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Annulus.SmoothGram

/-!
# Actual smooth annular area-to-energy approximation on the open cylinder

Uniformize the positive pullback regularization of the given smooth map.
The original weighted energy is bounded by the regularized area, whose
excess tends to zero. This constructs the modulus and parametrization;
extension to the closed cylinder is a separate boundary-regularity step.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)

private theorem strip_isOpen : IsOpen Strip :=
  isOpen_Ioo.preimage (EuclideanSpace.proj 1).continuous

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual regularized pullback dominates each diagonal Gram entry after any
differentiable source coordinate change. Source: Morgan--Tian (2007), Lemma 19.15, pp.
447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem regularizedPullback_comp_gram_le
    (g : RiemannianMetric n M) (f : Plane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) {delta : ℝ} (hdelta : 0 < delta)
    {F : Plane → Plane} {p : Plane} (hF : DifferentiableAt ℝ F p) (i : Fin 2) :
    m60AreaGram g (f ∘ F) p i i ≤
      m60AreaGram (m64RegularizedPullbackMetric g f hf delta hdelta) F p i i := by
  have hFm : MDifferentiableAt (𝓡 2) (𝓡 2) F p :=
    mdifferentiableAt_iff_differentiableAt.mpr hF
  have hcomp := mfderiv_comp p ((hf (F p)).mdifferentiableAt (by simp)) hFm
  unfold m60AreaGram
  rw [hcomp]
  exact m64RegularizedPullbackMetric_dominates g f hf delta hdelta (F p)
    (mfderiv (𝓡 2) (𝓡 2) F p (EuclideanSpace.basisFun (Fin 2) ℝ i))

private theorem weighted_density_eq_area
    {k : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) N] [IsManifold (𝓡 k) ∞ N]
    (g : RiemannianMetric k N) (f : Plane → N) {r : ℝ} (hr : 0 < r) (p : Plane)
    (hc : r * m60AreaGram g f p 0 0 = r⁻¹ * m60AreaGram g f p 1 1)
    (ho : m60AreaGram g f p 0 1 = 0) :
    (r * m60AreaGram g f p 0 0 + r⁻¹ * m60AreaGram g f p 1 1) / 2 =
      m60AreaDensity g f p := by
  let a := m60AreaGram g f p 0 0
  let b := m60AreaGram g f p 1 1
  have hscale : b = r ^ 2 * a := by
    have h := congrArg (fun x : ℝ => r * x) hc
    rw [← mul_assoc r r⁻¹, mul_inv_cancel₀ hr.ne', one_mul] at h
    nlinarith
  have hdet : Matrix.det (m60AreaGram g f p) = (r * a) ^ 2 := by
    rw [Matrix.det_fin_two, m60AreaGram_symm g f p 1 0, ho]
    simp only [zero_mul, sub_zero]
    change a * b = (r * a) ^ 2
    rw [hscale]
    ring
  have ha : 0 ≤ r * a := mul_nonneg hr.le (m60AreaGram_diagonal_nonneg g f p 0)
  have harea : m60AreaDensity g f p = r * a := by
    unfold m60AreaDensity
    rw [hdet, max_eq_right (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
  rw [harea, ← hc]
  dsimp only [a]
  ring

/-- A globally smooth annular map admits actual periodic open-cylinder coordinates with
weighted energy arbitrarily close to its original area. The modulus and coordinate map are
constructed from the given map. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; the
explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem exists_smooth_open_cylinder_energy_lt_area
    (g : RiemannianMetric n M) (f : Plane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) (eta : ℝ) (heta : 0 < eta) :
    ∃ (r : ℝ), 0 < r ∧ ∃ F : Plane → Plane,
      ContDiffOn ℝ ∞ F Strip ∧
      (∀ p ∈ Strip, F p ∈ scalarAnnulus) ∧
      InjOn F scalarCylinderFundamental ∧
      F '' scalarCylinderFundamental = scalarAnnulus ∧
      (∀ x s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
        F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s)) ∧
      ContMDiffOn (𝓡 2) (𝓡 n) ∞ (f ∘ F) Strip ∧
      IntegrableOn (fun p => (r * m60AreaGram g (f ∘ F) p 0 0 +
        r⁻¹ * m60AreaGram g (f ∘ F) p 1 1) / 2) scalarCylinderFundamental ∧
      (∫ p in scalarCylinderFundamental,
        (r * m60AreaGram g (f ∘ F) p 0 0 +
          r⁻¹ * m60AreaGram g (f ∘ F) p 1 1) / 2) <
        (∫ x in scalarAnnulus, m60AreaDensity g f x) + eta := by
  obtain ⟨delta, hdelta, hsmall⟩ :=
    m64RegularizedPullbackMetric_exists_annular_area_lt g f hf eta heta
  let q := m64RegularizedPullbackMetric g f hf delta hdelta
  obtain ⟨r, hr, F, hFs, hFmem, hFinj, hFimage, hFperiod, hFconf, hFA, hFarea⟩ :=
    exists_smooth_modulus_conformal_cylinder_area q
  have hu : ContMDiffOn (𝓡 2) (𝓡 n) ∞ (f ∘ F) Strip :=
    hf.comp_contMDiffOn (contMDiffOn_iff_contDiffOn.mpr hFs)
  let E : Plane → ℝ := fun p => (r * m60AreaGram g (f ∘ F) p 0 0 +
    r⁻¹ * m60AreaGram g (f ∘ F) p 1 1) / 2
  have hEnonneg (p : Plane) : 0 ≤ E p := by
    exact div_nonneg (add_nonneg
      (mul_nonneg hr.le (m60AreaGram_diagonal_nonneg g (f ∘ F) p 0))
      (mul_nonneg (inv_nonneg.mpr hr.le) (m60AreaGram_diagonal_nonneg g (f ∘ F) p 1)))
      (by norm_num)
  have hEbound {p : Plane} (hp : p ∈ scalarCylinderFundamental) :
      E p ≤ m60AreaDensity q F p := by
    have hFd := (hFs.contDiffAt (strip_isOpen.mem_nhds hp.1)).differentiableAt (by simp)
    have h0 := mul_le_mul_of_nonneg_left
      (regularizedPullback_comp_gram_le g f hf hdelta hFd 0) hr.le
    have h1 := mul_le_mul_of_nonneg_left
      (regularizedPullback_comp_gram_le g f hf hdelta hFd 1) (inv_nonneg.mpr hr.le)
    rw [← weighted_density_eq_area q F hr p (hFconf p hp.1).1 (hFconf p hp.1).2]
    exact div_le_div_of_nonneg_right (add_le_add h0 h1) (by norm_num)
  have hEc : ContinuousOn E Strip := by
    intro p hp
    have hup := hu.contMDiffAt (strip_isOpen.mem_nhds hp)
    have h0 := (m64AreaGram_entry_contDiffAt (g := g) hup 0 0).continuousAt
    have h1 := (m64AreaGram_entry_contDiffAt (g := g) hup 1 1).continuousAt
    have hc : ContinuousAt E p :=
      ((continuousAt_const.mul h0).add (continuousAt_const.mul h1)).div_const 2
    exact hc.continuousWithinAt
  have hEI : IntegrableOn E scalarCylinderFundamental := by
    apply hFA.mono' ((hEc.mono (fun _ hp => hp.1)).aestronglyMeasurable
      scalarCylinderFundamental_measurable)
    filter_upwards [ae_restrict_mem scalarCylinderFundamental_measurable] with p hp
    rw [Real.norm_of_nonneg (hEnonneg p)]
    exact hEbound hp
  refine ⟨r, hr, F, hFs, hFmem, hFinj, hFimage, hFperiod, hu, hEI, ?_⟩
  calc
    (∫ p in scalarCylinderFundamental, E p) ≤
        ∫ p in scalarCylinderFundamental, m60AreaDensity q F p := by
      apply integral_mono_ae hEI hFA
      filter_upwards [ae_restrict_mem scalarCylinderFundamental_measurable] with p hp
      exact hEbound hp
    _ = ∫ x in scalarAnnulus, m60AreaDensity q id x := hFarea
    _ < (∫ x in scalarAnnulus, m60AreaDensity g f x) + eta := hsmall

end PoincareMT.M64Uniformization

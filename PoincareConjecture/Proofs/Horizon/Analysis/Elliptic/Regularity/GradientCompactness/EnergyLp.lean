import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.ParametricProducts

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem memLp_top_spatial_partial_of_lipschitz
    {O U : Set E} (hO : IsOpen O) (hU : MeasurableSet U) (hUO : U ⊆ O)
    {I : Set ℝ} (hI : MeasurableSet I)
    {u : E × ℝ → ℝ} {L : ℝ≥0} (hu : LipschitzOnWith L u (O ×ˢ I)) (i : Fin d) :
    MemLp (fun z : ℝ × E =>
      fderiv ℝ (fun y => u (y, z.1)) z.2 (EuclideanSpace.single i 1))
      ∞ ((volume.restrict I).prod (volume.restrict U)) := by
  apply memLp_top_of_bound
    (aestronglyMeasurable_spatial_partial_of_lipschitz hO hU hUO hI hu i) (L : ℝ)
  have hmem : ∀ᵐ z ∂(volume.restrict I).prod (volume.restrict U), z ∈ I ×ˢ U := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (hI.prod hU)
  filter_upwards [hmem] with z hz
  have hl : LipschitzOnWith L (fun y => u (y, z.1)) O := by
    simpa only [mul_one, Function.comp_def] using hu.comp
      (LipschitzWith.prodMk_right z.1).lipschitzOnWith (fun y hy => ⟨hy, hz.1⟩)
  exact abs_partial_le_of_lipschitzOn hO hl (hUO hz.2) i

theorem memLp_top_spatial_gradient_quadratic_of_lipschitz
    {O U : Set E} (hO : IsOpen O) (hU : MeasurableSet U) (hUO : U ⊆ O)
    {I : Set ℝ} (hI : MeasurableSet I)
    {u : E × ℝ → ℝ} {L : ℝ≥0} (hu : LipschitzOnWith L u (O ×ˢ I))
    {A : ℝ × E → Fin d → Fin d → ℝ}
    (hA : ∀ i j, MemLp (fun z => A z i j) ∞
      ((volume.restrict I).prod (volume.restrict U))) :
    MemLp (fun z : ℝ × E => ∑ i, ∑ j, A z i j *
      fderiv ℝ (fun y => u (y, z.1)) z.2 (EuclideanSpace.single j 1) *
      fderiv ℝ (fun y => u (y, z.1)) z.2 (EuclideanSpace.single i 1))
      ∞ ((volume.restrict I).prod (volume.restrict U)) := by
  have hd (i) := memLp_top_spatial_partial_of_lipschitz hO hU hUO hI hu i
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  simpa only [Pi.mul_def] using (hd i).mul' (r := ∞)
    ((hd j).mul' (r := ∞) (hA i j))

theorem ae_eq_zero_of_ae_slices
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν] {f : X × Y → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hs : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f (x, y) = 0) : ∀ᵐ z ∂μ.prod ν, f z = 0 := by
  have hm : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, hf.mk f (x, y) = 0 := by
    filter_upwards [hs, Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with x hx hxm
    filter_upwards [hx, hxm] with y hy hym
    exact hym.symm.trans hy
  have hm0 := (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun hf.stronglyMeasurable_mk.measurable measurable_const)).mpr hm
  exact hf.ae_eq_mk.trans hm0

end Poincare.Analysis.Elliptic

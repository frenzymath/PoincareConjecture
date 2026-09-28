import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularCap
import PoincareConjecture.Proofs.M60.Mathlib.ConformalTrace
import PoincareConjecture.Proofs.M60.Mathlib.ConformalPlaneLaplacian
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff InnerProductSpace

noncomputable section

namespace PoincareConjecture.M60

local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ

def suBubbleInversion : LoopPlane → LoopPlane := EuclideanGeometry.inversion 0 2

theorem suBubbleInversion_geometry {z : LoopPlane} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ suBubbleInversion z ∧
      Function.Surjective (fderiv ℝ suBubbleInversion z) ∧
      (∀ i j : Fin 2,
        inner ℝ (fderiv ℝ suBubbleInversion z (b i))
          (fderiv ℝ suBubbleInversion z (b j)) =
            (2 / ‖z‖) ^ 4 * (if i = j then 1 else 0)) ∧
      |(fderiv ℝ suBubbleInversion z).det| = (2 / ‖z‖) ^ 4 := by
  let L := (ℝ ∙ z)ᗮ.reflection
  let c := (2 / ‖z‖) ^ 2
  have hc : 0 < c := by dsimp only [c]; positivity
  have hd : fderiv ℝ suBubbleInversion z = c • (L : LoopPlane →L[ℝ] LoopPlane) := by
    simpa only [suBubbleInversion, dist_zero_right, sub_zero, c, L] using
      (EuclideanGeometry.hasFDerivAt_inversion (R := (2 : ℝ)) hz).fderiv
  have hs : ContDiffAt ℝ ∞ suBubbleInversion z :=
    ContDiffAt.inversion contDiffAt_const contDiffAt_const contDiffAt_id hz
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro w
    refine ⟨L.symm (c⁻¹ • w), ?_⟩
    rw [hd, smul_apply]
    change c • L (L.symm (c⁻¹ • w)) = w
    rw [L.apply_symm_apply, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · intro i j
    rw [hd]
    change inner ℝ (c • L (b i)) (c • L (b j)) = _
    rw [real_inner_smul_left, real_inner_smul_right, L.inner_map_map,
      OrthonormalBasis.inner_eq_ite]
    dsimp only [c]
    ring
  · rw [hd]
    change |LinearMap.det (c • L.toLinearMap)| = _
    rw [LinearMap.det_smul, Submodule.det_reflection]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one, abs_of_pos hc]
    simp only [LoopPlane, finrank_euclideanSpace, Fintype.card_fin]
    dsimp only [c]
    ring

theorem suBubbleInversion_laplacian {z : LoopPlane} (hz : z ≠ 0) :
    fderiv ℝ (fderiv ℝ suBubbleInversion) z (b 0) (b 0) +
      fderiv ℝ (fderiv ℝ suBubbleInversion) z (b 1) (b 1) = 0 := by
  have h := suBubbleInversion_geometry hz
  apply laplacian_eq_zero_of_conformal_plane
    (h.1.of_le (WithTop.coe_le_coe.mpr le_top)) h.2.1
  · filter_upwards [isOpen_compl_singleton.mem_nhds hz] with y hy
    have hg := (suBubbleInversion_geometry hy).2.2.1
    simp only [hg, ite_true, mul_one]
  · filter_upwards [isOpen_compl_singleton.mem_nhds hz] with y hy
    have hg := (suBubbleInversion_geometry hy).2.2.1
    simp only [hg, Fin.zero_ne_one, ite_false, mul_zero]

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem suBubbleInversion_energy (g : RiemannianMetric n M) (f : LoopPlane → M)
    {z : LoopPlane} (hz : z ≠ 0)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (suBubbleInversion z)) :
    m60EnergyDensity g (f ∘ suBubbleInversion) z =
      |(fderiv ℝ suBubbleInversion z).det| * m60EnergyDensity g f (suBubbleInversion z) := by
  let A := mfderiv (𝓡 2) (𝓡 n) f (suBubbleInversion z)
  let B : LinearMap.BilinForm ℝ LoopPlane :=
    (g.inner (f (suBubbleInversion z))).toBilinForm.compl₁₂ A.toLinearMap A.toLinearMap
  have hgeom := suBubbleInversion_geometry hz
  have ha : 0 < (2 / ‖z‖) ^ 4 := by positivity
  have hh := sum_bilinear_conformal_basis B b
    (fun i => fderiv ℝ suBubbleInversion z (b i)) (by simp) ha hgeom.2.2.1
  rw [hgeom.2.2.2]
  simp only [m60EnergyDensity, Matrix.trace_fin_two, m60AreaGram]
  rw [mfderiv_comp z hf
    (hgeom.1.differentiableAt (by simp)).hasFDerivAt.hasMFDerivAt.mdifferentiableAt,
    mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.comp_apply, Function.comp_def]
  simp only [B, A, ContinuousLinearMap.toBilinForm_apply,
    LinearMap.compl₁₂_apply, Fin.sum_univ_two, ContinuousLinearMap.coe_coe] at hh
  erw [hh]
  ring_nf
  rfl

theorem suBubbleInversion_finite_energy (g : RiemannianMetric n M) (f : LoopPlane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) 1 f) (hfinite : Integrable (m60EnergyDensity g f)) :
    IntegrableOn (m60EnergyDensity g (f ∘ suBubbleInversion))
      (Metric.ball (0 : LoopPlane) 1 \ {0}) := by
  let S := Metric.ball (0 : LoopPlane) 1 \ {0}
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton _)
  have hk (z : LoopPlane) (hz : z ∈ S) :
      HasFDerivWithinAt suBubbleInversion (fderiv ℝ suBubbleInversion z) S z :=
    ((suBubbleInversion_geometry hz.2).1.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hi := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hk
    (EuclideanGeometry.inversion_injective (0 : LoopPlane) (by norm_num : (2 : ℝ) ≠ 0)).injOn
    (m60EnergyDensity g f)).mp hfinite.integrableOn
  exact hi.congr_fun (fun z hz =>
    (suBubbleInversion_energy g f hz.2 (hf.mdifferentiable (by simp) _)).symm) hS

end PoincareConjecture.M60

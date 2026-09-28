import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PhaseGradient
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.BoundaryLogarithmicOscillation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction









set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

open Proofs.M58

local notation "S" => interior m64AnnulusDomain
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)



theorem upperBoundaryDisk_subset_interior {x rho : ℝ}
    (hx : rho < x) (hP : x + rho < curvePeriod) (hr : rho < 1) :
    upperBoundaryDisk x rho ⊆ S := by
  intro p hp
  have hd := Metric.mem_closedBall.mp hp.1
  rw [dist_eq_norm] at hd
  have h0 := (PiLp.norm_apply_le (p - annulusPoint x 0) 0).trans hd
  have h1 := (PiLp.norm_apply_le (p - annulusPoint x 0) 1).trans hd
  change ‖p 0 - x‖ ≤ rho at h0
  change ‖p 1 - 0‖ ≤ rho at h1
  rw [Real.norm_eq_abs] at h0 h1
  apply (m64AnnulusInterior_coordinates p).mpr
  have ha0 := abs_le.mp h0
  have ha1 := abs_le.mp h1
  exact ⟨by linarith [ha0.1], by linarith [ha0.2], hp.2, by linarith [ha1.2]⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem circle_phase_energy_le_weighted_annulus
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map S)
    (L : LoopPlane → ℝ) (hL : ContDiffOn ℝ 1 L S)
    (hquot : ∀ p ∈ m64AnnulusDomain, P.circle.quotient (L p) = (A.map p).2)
    {lo hi r : ℝ} (hlo : 0 < lo) (hr : r ∈ Icc lo hi)
    (hE : IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
      r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain) :
    IntegrableOn (phaseGradientDensity L) S ∧
      (∫ p in S, phaseGradientDensity L p) ≤
        2 * max lo⁻¹ hi * m64ClassicalWeightedGramEnergy (P.flow.metric t) A r := by
  let W := fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
    r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2
  have hrpos : 0 < r := hlo.trans_le hr.1
  have h0 : 1 ≤ max lo⁻¹ hi * r := by
    have hh := mul_le_mul_of_nonneg_left hr.1 (inv_nonneg.mpr hlo.le)
    rw [inv_mul_cancel₀ hlo.ne'] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrpos.le)
  have h1 : 1 ≤ max lo⁻¹ hi * r⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right (hr.2.trans (le_max_right lo⁻¹ hi))
      (inv_nonneg.mpr hrpos.le)
    simpa only [mul_inv_cancel₀ hrpos.ne'] using hh
  have hbound (p : LoopPlane) (hp : p ∈ S) :
      phaseGradientDensity L p ≤ (2 * max lo⁻¹ hi) * W p := by
    have hgrad (i : Fin 2) := local_circle_phase_column_sq_le_gram P t A.map L p
      (((hA p hp).contMDiffAt (isOpen_interior.mem_nhds hp)).mdifferentiableAt one_ne_zero)
      (((hL p hp).contDiffAt (isOpen_interior.mem_nhds hp)).differentiableAt one_ne_zero)
      (show P.circle.quotient ∘ L =ᶠ[𝓝 p] Prod.snd ∘ A.map from by
        filter_upwards [isOpen_interior.mem_nhds hp] with q hq
        exact hquot q (interior_subset hq)) i
    have hg0 : (fderiv ℝ L p e0) ^ 2 ≤ m60AreaGram (P.flow.metric t) A.map p 0 0 := by
      simpa only [EuclideanSpace.basisFun_apply] using hgrad 0
    have hg1 : (fderiv ℝ L p e1) ^ 2 ≤ m60AreaGram (P.flow.metric t) A.map p 1 1 := by
      simpa only [EuclideanSpace.basisFun_apply] using hgrad 1
    have hh0 := mul_le_mul_of_nonneg_right h0
      (m60AreaGram_diagonal_nonneg (P.flow.metric t) A.map p 0)
    have hh1 := mul_le_mul_of_nonneg_right h1
      (m60AreaGram_diagonal_nonneg (P.flow.metric t) A.map p 1)
    dsimp only [phaseGradientDensity, W]
    nlinarith
  have hDf : ContinuousOn (fderiv ℝ L) S :=
    (hL.fderiv_of_isOpen isOpen_interior (m := 0) (by norm_num)).continuousOn
  have hc : ContinuousOn (phaseGradientDensity L) S :=
    ((hDf.clm_apply continuousOn_const).pow 2).add
      ((hDf.clm_apply continuousOn_const).pow 2)
  have hWi : IntegrableOn W S := hE.mono_set interior_subset
  have hphase : IntegrableOn (phaseGradientDensity L) S := by
    apply (hWi.const_mul (2 * max lo⁻¹ hi)).mono_nonneg
      (hc.aestronglyMeasurable isOpen_interior.measurableSet)
      (ae_of_all _ (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _)))
    exact (ae_restrict_mem isOpen_interior.measurableSet).mono hbound
  refine ⟨hphase, ?_⟩
  calc
    _ ≤ ∫ p in S, (2 * max lo⁻¹ hi) * W p :=
      setIntegral_mono_on hphase (hWi.const_mul _) isOpen_interior.measurableSet hbound
    _ = (2 * max lo⁻¹ hi) * ∫ p in S, W p := integral_const_mul _ _
    _ = _ := by
      unfold m64ClassicalWeightedGramEnergy
      rw [m64Annulus_restrict_closed_eq_interior]




theorem annulus_lower_phase_logarithmic_bound
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {c0 c1 : ℝ → P.charts.Point} (A : M64Annulus (P.flow.metric t) c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 A.map S)
    (L0 : ℝ → ℝ) (hL0 : Continuous L0)
    (hzero : ∀ x ∈ Icc (0 : ℝ) curvePeriod, P.circle.quotient (L0 x) = (c0 x).2)
    (hmono : MonotoneOn L0 (Icc (0 : ℝ) curvePeriod))
    {lo hi r : ℝ} (hlo : 0 < lo) (hr : r ∈ Icc lo hi)
    (hE : IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) A.map p 0 0 +
      r⁻¹ * m60AreaGram (P.flow.metric t) A.map p 1 1) / 2) m64AnnulusDomain)
    {x rho : ℝ} (hrho : 0 < rho) (hx : rho < x)
    (hP : x + rho < curvePeriod) (hradius : rho < 1) {N : ℕ} (hN : 0 < N) :
    (L0 (x + rho * Real.exp (-(N : ℝ))) - L0 (x - rho * Real.exp (-(N : ℝ)))) ^ 2 ≤
      (2 * Real.pi * max lo⁻¹ hi) * m64ClassicalWeightedGramEnergy (P.flow.metric t) A r / N := by
  obtain ⟨L, hLc, hL, hquot, hb, -⟩ :=
    annulus_exists_continuous_phase_with_gradient_bound P t A hA L0 hL0 hzero
  obtain ⟨hphase, henergy⟩ := circle_phase_energy_le_weighted_annulus P t A hA L hL
    hquot hlo hr hE
  have hsub := upperBoundaryDisk_subset_interior hx hP hradius
  have hmonoL : MonotoneOn (fun y => L (annulusPoint y 0)) (Icc (0 : ℝ) curvePeriod) := by
    intro y hy z hz hyz
    change L (annulusPoint y 0) ≤ L (annulusPoint z 0)
    rw [hb y hy, hb z hz]
    exact hmono hy hz hyz
  have hosc := boundary_logarithmic_oscillation L hLc hL hmonoL hrho hx hP hradius
    (hphase.mono_set hsub) hN
  have hdisk : (∫ p in upperBoundaryDisk x rho, phaseGradientDensity L p) ≤
      ∫ p in S, phaseGradientDensity L p :=
    setIntegral_mono_set hphase
      (ae_of_all _ (fun p => add_nonneg (sq_nonneg _) (sq_nonneg _))) (ae_of_all _ hsub)
  have hRN : 0 ≤ rho * Real.exp (-(N : ℝ)) := by positivity
  have hRle : rho * Real.exp (-(N : ℝ)) ≤ rho :=
    mul_le_of_le_one_right hrho.le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N)))
  rw [hb _ ⟨by linarith, by linarith⟩, hb _ ⟨by linarith, by linarith⟩] at hosc
  have hfinal := hosc.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hdisk.trans henergy) Real.pi_pos.le) (by positivity : (0 : ℝ) ≤ N))
  exact hfinal.trans_eq (by ring)

end PoincareConjecture.M64

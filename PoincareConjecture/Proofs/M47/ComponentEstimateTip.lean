import PoincareConjecture.Proofs.M47.ComponentEstimateGeometry
import PoincareConjecture.Proofs.M36.MetricComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_NormalizedCoefficients
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_LocalScalarTransport
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceScalarContinuity
import Mathlib.Analysis.Calculus.ContDiff.Bounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => StandardCapSpace

noncomputable local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem standard_tip_scalar_gt_three_quarters (g₀ : StandardInitialMetric) :
    (3 / 4 : ℝ) < g₀.connection.scalarCurvature 0 := by
  obtain ⟨r, hr, htip⟩ := g₀.tip_sectional_curvature
  have hzero : (0 : E) ∈ g₀.metric.ball 0 r := by
    change g₀.metric.edist 0 0 < ENNReal.ofReal r
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have h := six_mul_lt_scalar_of_sectional_lower g₀.connection 0 (1 / 8)
    (fun v w hvw => by rw [htip 0 hzero v w hvw]; norm_num)
  norm_num at h
  exact h

private theorem coefficient_jet_norm_le_bilinear
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiffAt ℝ ∞ B 0)
    (j : ℕ) (a b : Fin 3) :
    ‖iteratedFDeriv ℝ j (fun y => B y (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b)) 0‖ ≤ ‖iteratedFDeriv ℝ j B 0‖ := by
  have hj : (j : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have h1 := norm_iteratedFDeriv_clm_apply_const hB hj
    (c := EuclideanSpace.basisFun (Fin 3) ℝ a)
  have h2 := norm_iteratedFDeriv_clm_apply_const
    (hB.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))) hj
    (c := EuclideanSpace.basisFun (Fin 3) ℝ b)
  simp only [OrthonormalBasis.norm_eq_one, one_mul] at h1 h2
  exact h2.trans h1

theorem exists_tip_scalar_accuracy (g₀ : StandardInitialMetric) :
    ∃ eta₀ : ℝ, 0 < eta₀ ∧ eta₀ ≤ 1 / 4 ∧
      ∀ (S : GeneralizedSliceCarrier.{u}) (g : RiemannianMetric 3 S.carrier)
        (D : LeviCivitaData g) (tip : S.carrier) (scale eta : ℝ)
        (_Q : SurgeryCapClose g₀ S g tip scale eta),
        eta ≤ eta₀ → (3 / 4 : ℝ) < scale ^ 2 * D.scalarCurvature tip := by
  have hbase := standard_tip_scalar_gt_three_quarters g₀
  obtain ⟨zeta, hzeta, hscalar⟩ := M34.capPersistence_exists_scalar_tolerance
    g₀.connection (0 : E) (sub_pos.mpr hbase)
  choose B hB hbound using fun j : Fin 3 =>
    SurgeryCapClose.exists_normalized_coefficient_jet_bound.{u}
      g₀ (K := ({0} : Set E)) isCompact_singleton j.1
  let Bmax := max (B 0) (max (B 1) (B 2))
  have hBmax : 0 < Bmax := (hB 0).trans_le (le_max_left _ _)
  have hBj (j : Fin 3) : B j ≤ Bmax := by
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  let eta₀ := min (1 / 4 : ℝ) (zeta / (Bmax + 1))
  have heta₀ : 0 < eta₀ := lt_min (by norm_num) (div_pos hzeta (by positivity))
  refine ⟨eta₀, heta₀, min_le_left _ _, ?_⟩
  intro S g D tip scale eta Q heta
  have hsmall : eta ≤ 1 / 4 := heta.trans (min_le_left _ _)
  have horder : 2 ≤ ⌊eta⁻¹⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_ofNat, inv_eq_one_div, le_div_iff₀ Q.eta_pos]
    linarith
  have hzero : (0 : E) ∈ g₀.metric.ball 0 eta⁻¹ := by
    change g₀.metric.edist 0 0 < ENNReal.ofReal eta⁻¹
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr (inv_pos.mpr Q.eta_pos)
  have hsingleton : ({0} : Set E) ⊆ g₀.metric.ball 0 eta⁻¹ := by
    simpa only [singleton_subset_iff] using hzero
  have herrorSize : Bmax * eta ≤ zeta := by
    have hb := (le_div_iff₀ (show 0 < Bmax + 1 by positivity)).1
      (heta.trans (min_le_right _ _))
    nlinarith [Q.eta_pos]
  have hinv (y : E) (hy : y ∈ g₀.metric.ball 0 eta⁻¹) :
      (mfderiv (𝓡 3) (𝓡 3) Q.map y).IsInvertible :=
    ⟨(Q.toPartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hy).mfderivToContinuousLinearEquiv
      (by simp), rfl⟩
  obtain ⟨gE, DE, V, hV, hzeroV, hVsub, hmetric⟩ :=
    RiemannianMetric.exists_local_realization Q.toPartialDiffeomorph.open_source hzero
      Q.normalizedCoefficients Q.contDiffOn_normalizedCoefficients
      (fun y _ v w => by
        simp only [SurgeryCapClose.normalizedCoefficients_apply, g.symm])
      (fun y hy v hv => by
        change 0 < scale⁻¹ ^ 2 * g.inner (Q.map y)
          (mfderiv (𝓡 3) (𝓡 3) Q.map y v) (mfderiv (𝓡 3) (𝓡 3) Q.map y v)
        apply mul_pos (sq_pos_of_pos (inv_pos.mpr Q.scale_pos))
        apply g.pos
        intro hz
        apply hv
        exact (hinv y hy).injective (by simpa only [map_zero] using hz))
  have hcoeff : gE.euclideanCoefficients =ᶠ[𝓝 (0 : E)] Q.normalizedCoefficients :=
    eventually_of_mem (hV.mem_nhds hzeroV) hmetric
  have hdiff : (gE.euclideanCoefficients - g₀.metric.euclideanCoefficients) =ᶠ[𝓝 (0 : E)]
      (Q.normalizedCoefficients - g₀.metric.euclideanCoefficients) :=
    hcoeff.sub Filter.EventuallyEq.rfl
  have hjet (j : ℕ) (hj : j ≤ 2) :
      ‖iteratedFDeriv ℝ j (gE.euclideanCoefficients - g₀.metric.euclideanCoefficients) 0‖ ≤
        zeta := by
    rw [(hdiff.iteratedFDeriv (𝕜 := ℝ) (n := j)).self_of_nhds]
    have h := hbound ⟨j, by omega⟩ S g tip scale eta Q (hj.trans horder)
      hsingleton 0 (mem_singleton 0)
    exact h.trans ((mul_le_mul_of_nonneg_right (hBj ⟨j, by omega⟩) Q.eta_pos.le).trans
      herrorSize)
  have hclose := hscalar gE DE (fun j hj a b =>
    (coefficient_jet_norm_le_bilinear
      ((gE.contDiffAt_euclideanCoefficients 0).sub
        (g₀.metric.contDiffAt_euclideanCoefficients 0)) j a b).trans (hjet j hj))
  have hpositive : (3 / 4 : ℝ) < DE.scalarCurvature 0 := by
    have h := (abs_lt.1 hclose).1
    linarith
  have hpullback (y : E) (hy : y ∈ V) (v w : E) :
      g.inner (Q.map y) (mfderiv (𝓡 3) (𝓡 3) Q.map y v)
          (mfderiv (𝓡 3) (𝓡 3) Q.map y w) = scale ^ 2 * gE.inner y v w := by
    have hm := congrArg (fun A => A v w) (hmetric y hy)
    change gE.inner y v w = scale⁻¹ ^ 2 * g.inner (Q.map y)
      (mfderiv (𝓡 3) (𝓡 3) Q.map y v) (mfderiv (𝓡 3) (𝓡 3) Q.map y w) at hm
    rw [hm]
    field_simp [Q.scale_pos.ne']
  have hscaled := M44.scalar_eq_of_local_homothety DE D hV
    (Q.map_smooth.mono hVsub) (fun y hy => hinv y (hVsub hy))
    (sq_pos_of_pos Q.scale_pos) hpullback hzeroV
  rw [Q.map_tip] at hscaled
  have heq : scale ^ 2 * D.scalarCurvature tip = DE.scalarCurvature 0 := by
    rw [hscaled]
    field_simp [Q.scale_pos.ne']
  rwa [heq]

end PoincareConjecture.M47

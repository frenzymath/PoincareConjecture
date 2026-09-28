import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedSpatialSlices
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.HolderAssembly
import Mathlib.Topology.UniformSpace.UniformConvergence












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold



theorem generalized_slice_coefficient_eq
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) (k : ℕ) (t : ℝ)
    (ht : t ∈ Icc (-G.exhaustion.time k) 0) (q : G.limit.carrier.carrier)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ (extChartAt (𝓡 3) q).target)
    (hstage : (extChartAt (𝓡 3) q).symm x ∈ G.exhaustion.space k)
    (a b : Fin 3) :
    (normalizedBlowupSliceMetric S (G.subsequence k) t).pullbackCoefficients
        (generalizedSliceHomeomorph G k t ht ∘ (extChartAt (𝓡 3) q).symm) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      blowupPullbackCoefficient (G.embedding k) q a b (t, x) := by
  let c := extChartAt (𝓡 3) q
  let e := generalizedSliceHomeomorph G k t ht
  have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e (c.symm x) :=
    generalizedSliceHomeomorph_contMDiffAt G k t ht hstage
  have hc : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hx)
  have hderiv := mfderiv_comp x (he.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  simp only [blowupPullbackCoefficient, dif_pos ht]
  change (normalizedBlowupSliceMetric S (G.subsequence k) t).inner (e (c.symm x))
      (mfderiv (𝓡 3) (𝓡 3) (e ∘ c.symm) x (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3) (e ∘ c.symm) x (EuclideanSpace.basisFun (Fin 3) ℝ b)) = _
  rw [hderiv]
  rfl




theorem tendstoUniformlyOn_generalized_slice_coefficients
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    (N : ℕ) (hNt : ∀ k : ℕ, t ∈ Icc (-G.exhaustion.time (k + N)) 0)
    (q : G.limit.carrier.carrier) {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 3) q).target) :
    TendstoUniformlyOn
      (fun k => (normalizedBlowupSliceMetric S (G.subsequence (k + N)) t).pullbackCoefficients
        (generalizedSliceHomeomorph G (k + N) t (hNt k) ∘ (extChartAt (𝓡 3) q).symm))
      ((G.limit.flow.metric t).pullbackCoefficients (extChartAt (𝓡 3) q).symm) atTop K := by
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) q
  let A (k : ℕ) :=
    (normalizedBlowupSliceMetric S (G.subsequence (k + N)) t).pullbackCoefficients
      (generalizedSliceHomeomorph G (k + N) t (hNt k) ∘ c.symm)
  let B := (G.limit.flow.metric t).pullbackCoefficients c.symm
  have hc : ContinuousOn c.symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKt
  obtain ⟨j, hj⟩ := exists_generalized_exhaustion_stage G (hK.image_of_continuousOn hc)
  have htest : ({t} ×ˢ K) ⊆ {p | p ∈ blowupMetricChartDomain G.limit q ∧
      c.symm p.2 ∈ G.exhaustion.space j} := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    have hst : s = t := mem_singleton_iff.mp hs
    subst s
    exact ⟨⟨ht, hKt hx⟩, hj (mem_image_of_mem _ hx)⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro epsilon hepsilon
  obtain ⟨L, hjL, hL⟩ := G.pullback_metric_CInfinity q j 0 ({t} ×ˢ K)
    (isCompact_singleton.prod hK) htest (epsilon / 18) (by positivity)
  filter_upwards [eventually_ge_atTop L] with k hk x hx
  have hkN : L ≤ k + N := by omega
  have hstage : c.symm x ∈ G.exhaustion.space (k + N) :=
    G.exhaustion.space_increasing (hjL.trans hkN) (hj (mem_image_of_mem _ hx))
  have hentry (a b : Fin 3) :
      |(A k x - B x) (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)| ≤ epsilon / 18 := by
    have H := (hL (k + N) hkN).2 a b (t, x) ⟨mem_singleton t, hx⟩
    rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, Real.dist_eq] at H
    rw [← generalized_slice_coefficient_eq G (k + N) t (hNt k) q (hKt hx)
      hstage a b] at H
    exact H.le
  have hnorm := HarmonicCoordinates.norm_bilinear_le_dim_sq_mul_of_entries
    (A k x - B x) (show 0 ≤ epsilon / 18 by positivity) hentry
  calc
    dist (B x) (A k x) = ‖A k x - B x‖ := by rw [dist_eq_norm, norm_sub_rev]
    _ ≤ (3 : ℝ) ^ 2 * (epsilon / 18) := hnorm
    _ < epsilon := by linarith

end PoincareConjecture.M30

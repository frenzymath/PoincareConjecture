import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Analysis.Calculus

theorem tendstoUniformlyOn_bilinear_of_basis_entries
    {n : ℕ} {X : Type*} {K : Set X}
    {A : ℕ → X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    {B : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (hentry : ∀ i j : Fin n, TendstoUniformlyOn
      (fun k x ↦ A k x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
      (fun x ↦ B x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
      atTop K) : TendstoUniformlyOn A B atTop K := by
  apply (Metric.tendstoUniformlyOn_iff (F := A) (f := B)).mpr
  intro ε hε
  let δ := ε / ((n : ℝ) ^ 2 + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hfinite : ∀ᶠ k in atTop, ∀ i j : Fin n, ∀ x ∈ K,
      dist (B x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
        (A k x (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) < δ :=
    eventually_all.mpr (fun i ↦ eventually_all.mpr (fun j ↦
      Metric.tendstoUniformlyOn_iff.mp (hentry i j) δ hδ))
  filter_upwards [hfinite] with k hk x hx
  rw [dist_eq_norm (B x) (A k x)]
  have hb := PoincareConjecture.HarmonicCoordinates.norm_bilinear_le_dim_sq_mul_of_entries
    (B x - A k x) hδ.le (fun i j ↦ ?_)
  · apply hb.trans_lt
    have hden : 0 < (n : ℝ) ^ 2 + 1 := by positivity
    calc (n : ℝ) ^ 2 * δ < ((n : ℝ) ^ 2 + 1) * δ :=
          mul_lt_mul_of_pos_right (by linarith) hδ
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hden)
  · simpa only [ContinuousLinearMap.sub_apply, dist_eq_norm, Real.norm_eq_abs] using (hk i j x hx).le

end Poincare.Analysis.Calculus

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem tendstoUniformlyOn_pulledChartCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier)
    (t : ℝ) (ht : t ∈ Ioo a b)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt (𝓡 n) q).target) :
    TendstoUniformlyOn (fun k ↦ G.pulledChartCoefficients q k t)
      ((G.limitFlow.metricAt t).pullbackCoefficients (extChartAt (𝓡 n) q).symm) atTop K := by
  have hc := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  have hentry (i l : Fin n) : TendstoUniformlyOn
      (fun k y ↦ G.pulledChartCoefficients q k t y
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ l))
      (fun y ↦ (G.limitFlow.metricAt t).pullbackCoefficients (extChartAt (𝓡 n) q).symm y
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ l)) atTop K := by
    have hjet := G.tendstoUniformlyOn_coordinate_spatial_metricJet q 0 i l t ht K hK hKc
    have hev := ContinuousMultilinearMap.uniformContinuous_eval_const
      (𝕜 := ℝ) (F := ℝ) (0 : Fin 0 → EuclideanSpace ℝ (Fin n))
    have hval := hev.comp_tendstoUniformlyOn hjet
    simp only [Function.comp_def, iteratedFDeriv_zero_apply] at hval
    apply hval.congr
    filter_upwards [eventually_ge_atTop j] with k hk y hy
    exact (G.pulledChartCoefficients_basis_eq q k t ht (hKc hy)
      (G.exhaustion_monotone hk (hj (mem_image_of_mem _ hy))) i l).symm
  exact Poincare.Analysis.Calculus.tendstoUniformlyOn_bilinear_of_basis_entries hentry

theorem tendstoLocallyUniformlyOn_pulledChartCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    TendstoLocallyUniformlyOn (fun k ↦ G.pulledChartCoefficients q k t)
      ((G.limitFlow.metricAt t).pullbackCoefficients (extChartAt (𝓡 n) q).symm)
      atTop (extChartAt (𝓡 n) q).target := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact
    (isOpen_extChartAt_target (I := 𝓡 n) q)).mpr
  intro K hKc hK
  exact G.tendstoUniformlyOn_pulledChartCoefficients q t ht hK hKc

end PoincareConjecture.PointedGeometricConvergence

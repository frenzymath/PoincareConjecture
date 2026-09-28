import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Continuation.Geodesic
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {γ : ℝ → M} {s : Set ℝ}

theorem IsGeodesicOn.contMDiffOn (hγ : g.IsGeodesicOn γ s) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ s := by
  intro t ht
  obtain ⟨p, q, w, h⟩ := hγ t ht
  obtain ⟨U, hUsub, hUopen, htU⟩ := mem_nhds_iff.mp h
  have hq : ContDiffOn ℝ 1 q U := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen hUopen]
    refine ⟨fun u hu => (hUsub hu).2.2.1.differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    rw [contDiffOn_zero]
    apply (show ContinuousOn w U from fun u hu =>
      (hUsub hu).2.2.2.continuousAt.continuousWithinAt).congr
    intro u hu
    exact (hUsub hu).2.2.1.deriv
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1
      (fun u => (extChartAt (𝓡 n) p).symm (q u)) U :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := 1) p).comp
      (contMDiffOn_iff_contDiffOn.mpr hq) (fun u hu => (hUsub hu).2.1)
  exact ((hcomp.contMDiffAt (hUopen.mem_nhds htU)).congr_of_eventuallyEq
    (h.mono fun u hu => hu.1)).contMDiffWithinAt

theorem IsGeodesicOn.hasDerivAt_tangentNorm_zero (hγ : g.IsGeodesicOn γ s)
    {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (fun u =>
      g.tangentNorm (γ u) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ u 1)) 0 t := by
  obtain ⟨p, q, w, h⟩ := hγ t ht
  obtain ⟨c, d, htcd, hcd⟩ := mem_nhds_iff_exists_Ioo_subset.mp h
  let B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
  have henergy : ∀ u ∈ Ioo c d,
      HasDerivAt (fun v => B (q v) (w v) (w v)) 0 u := by
    intro u hu
    have hqu := (hcd hu).2.1
    exact hasDerivAt_coordinate_geodesic_energy
      (((g.contDiffOn_chartCoefficients p (q u) hqu).contDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds hqu)).differentiableAt
        (by simp)) (g.isInvertible_chartCoefficients p hqu)
      (fun v z => g.symm _ _ _) (hcd hu).2.2.1 (hcd hu).2.2.2
  have hconst : ∀ u ∈ Ioo c d, B (q u) (w u) (w u) = B (q t) (w t) (w t) := by
    intro u hu
    exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo c d).isPreconnected
      (fun v hv => (henergy v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (henergy v hv).deriv) hu htcd
  apply (hasDerivAt_const t (Real.sqrt (B (q t) (w t) (w t)))).congr_of_eventuallyEq
  have heq : γ =ᶠ[𝓝 t] fun u => (extChartAt (𝓡 n) p).symm (q u) :=
    h.mono fun u hu => hu.1
  filter_upwards [eventually_eventually_nhds.mpr heq,
    Ioo_mem_nhds htcd.1 htcd.2] with u hequ hu
  change γ =ᶠ[𝓝 u] (fun v => (extChartAt (𝓡 n) p).symm (q v)) at hequ
  rw [hequ.mfderiv_eq, hequ.self_of_nhds,
    g.tangentNorm_chart_curve p (hcd hu).2.2.1 (hcd hu).2.1, hconst u hu]

theorem IsGeodesicOn.exists_constant_tangentNorm {a b : ℝ}
    (hγ : g.IsGeodesicOn γ (Ioo a b)) (hab : a < b) :
    ∃ C : ℝ≥0, ∀ t ∈ Ioo a b,
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) = C := by
  let t₀ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := by dsimp [t₀]; constructor <;> linarith
  refine ⟨⟨g.tangentNorm (γ t₀) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t₀ 1),
    Real.sqrt_nonneg _⟩, fun t ht => ?_⟩
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun u hu => (hγ.hasDerivAt_tangentNorm_zero hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hγ.hasDerivAt_tangentNorm_zero hu).deriv) ht ht₀

theorem IsGeodesicOn.edist_le_of_tangentNorm_eq {a b : ℝ}
    (hγ : g.IsGeodesicOn γ (Ioo a b)) {C : ℝ≥0}
    (hC : ∀ t ∈ Ioo a b,
      g.tangentNorm (γ t) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) = C)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    g.edist (γ s) (γ t) ≤ C * EDist.edist s t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hforward : ∀ {u v : ℝ}, u ∈ Ioo a b → v ∈ Ioo a b → u ≤ v →
      g.edist (γ u) (γ v) ≤ C * EDist.edist u v := by
    intro u v hu hv huv
    have hsub : Icc u v ⊆ Ioo a b :=
      fun z hz => ⟨hu.1.trans_le hz.1, hz.2.trans_lt hv.2⟩
    have hdist : g.edist (γ u) (γ v) ≤ g.pathELength γ u v :=
      Manifold.riemannianEDist_le_pathELength (hγ.contMDiffOn.mono hsub) rfl rfl huv
    have hlength : g.pathELength γ u v = C * ENNReal.ofReal (v - u) := by
      rw [pathELength_eq_lintegral_tangentNorm]
      have heq : (fun z => ENNReal.ofReal
          (g.tangentNorm (γ z) (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ z 1))) =ᵐ[
            volume.restrict (Icc u v)] fun _ => (C : ℝ≥0∞) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
        rw [hC z (hsub hz), ENNReal.ofReal_coe_nnreal]
      rw [lintegral_congr_ae heq, lintegral_const, Measure.restrict_apply_univ,
        Real.volume_Icc]
    have het : EDist.edist u v = ENNReal.ofReal (v - u) := by
      rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huv), neg_sub]
    rw [het]
    exact hdist.trans_eq hlength
  rcases le_total s t with hst | hts
  · exact hforward hs ht hst
  · simpa only [edist, Manifold.riemannianEDist_comm, edist_comm] using
      hforward ht hs hts

theorem IsGeodesicOn.exists_edist_le_mul {a b : ℝ}
    (hγ : g.IsGeodesicOn γ (Ioo a b)) (hab : a < b) :
    ∃ C : ℝ≥0, ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b,
      g.edist (γ s) (γ t) ≤ C * EDist.edist s t := by
  obtain ⟨C, hC⟩ := hγ.exists_constant_tangentNorm hab
  exact ⟨C, fun _ hs _ ht => hγ.edist_le_of_tangentNorm_eq hC hs ht⟩

end PoincareConjecture.RiemannianMetric

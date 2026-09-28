import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_InteriorMetricSegment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.MetricArc













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture





theorem m64Intrinsic_constrained_minimizer_interior_geodesic
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {γ : ℝ → AnnulusCoordinates} {L : ℝ}
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (γ s) (γ t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
      ∀ τ : ℝ → AnnulusCoordinates, ContinuousOn τ (Icc 0 1) →
        τ 0 = γ a → τ 1 = γ b → MapsTo τ (Icc 0 1) K →
        ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G τ 0 1) :
    G.IsGeodesicOn γ {u | u ∈ Ioo 0 L ∧ γ u ∈ interior K} ∧
      ∀ u ∈ Ioo 0 L, γ u ∈ interior K → ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ u := by
  have hpoint (u : ℝ) (hu : u ∈ Ioo 0 L) (hKu : γ u ∈ interior K) :
      G.IsGeodesicOn γ {u} ∧ ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ u := by
    obtain ⟨epsilon, hepsilon, _, hmetric⟩ :=
      m64Intrinsic_constrained_minimizer_local_metric_segment G hK hlip hmin hu hKu
    obtain ⟨hgeo, hsmooth⟩ := G.isGeodesicOn_and_contMDiffOn_of_edist_affine_segment
      (γ := γ) (a := u - epsilon) (b := u + epsilon) (c := 1) zero_le_one (by
        intro s hs t ht
        simpa only [one_mul] using
          hmetric s (Ioo_subset_Icc_self hs) t (Ioo_subset_Icc_self ht))
    have hu' : u ∈ Ioo (u - epsilon) (u + epsilon) := by constructor <;> linarith
    refine ⟨fun t ht => ?_, hsmooth.contMDiffAt (isOpen_Ioo.mem_nhds hu')⟩
    have ht' : t = u := ht
    subst t
    exact hgeo u hu'
  exact ⟨fun u hu => (hpoint u hu.1 hu.2).1 u rfl,
    fun u hu hKu => (hpoint u hu hKu).2⟩






theorem m64Intrinsic_exists_region_minimizer_geodesic_interior
    (G : RiemannianMetric 2 AnnulusCoordinates) {K : Set AnnulusCoordinates}
    (hK : IsCompact K) {p q : AnnulusCoordinates} {σ : ℝ → AnnulusCoordinates}
    (hc : ContinuousOn σ (Icc 0 1)) (h0 : σ 0 = p) (h1 : σ 1 = q)
    (hconf : MapsTo σ (Icc 0 1) K) {B : ℝ}
    (hB : m64IntrinsicCurveVariation G σ 0 1 ≤ ENNReal.ofReal B) :
    ∃ (γ : ℝ → AnnulusCoordinates) (L : ℝ), 0 ≤ L ∧ L ≤ max B 0 ∧
      ContinuousOn γ (Icc 0 L) ∧ γ 0 = p ∧ γ L = q ∧ MapsTo γ (Icc 0 L) K ∧
      InjOn γ (Icc 0 L) ∧
      (∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L,
        m64IntrinsicCurveVariation G γ a b = ENNReal.ofReal (b - a)) ∧
      G.IsGeodesicOn γ {u | u ∈ Ioo 0 L ∧ γ u ∈ interior K} ∧
      (∀ u ∈ Ioo 0 L, γ u ∈ interior K → ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ u) ∧
      (∀ a ∈ Icc 0 L, ∀ b ∈ Icc 0 L, a ≤ b →
        ∀ τ : ℝ → AnnulusCoordinates, ContinuousOn τ (Icc 0 1) →
          τ 0 = γ a → τ 1 = γ b → MapsTo τ (Icc 0 1) K →
          ENNReal.ofReal (b - a) ≤ m64IntrinsicCurveVariation G τ 0 1) := by
  obtain ⟨γ, L, hL, hLB, hγc, hγ0, hγL, hγconf, hγinj, hγlip, hγvar, hγmin⟩ :=
    m64Intrinsic_exists_embedded_region_minimizer G hK hc h0 h1 hconf hB
  obtain ⟨hgeo, hsmooth⟩ :=
    m64Intrinsic_constrained_minimizer_interior_geodesic G hK hγlip hγmin
  exact ⟨γ, L, hL, hLB, hγc, hγ0, hγL, hγconf, hγinj, hγvar, hgeo, hsmooth, hγmin⟩

end PoincareConjecture

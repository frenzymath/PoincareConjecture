import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicSideRegularity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LastContactTangency











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_constrained_minimizer_geodesic_side_agreement
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha) {a b p : ℝ}
    (hinj : InjOn alpha (Icc a b)) (hp : p ∈ Ioo a b) (hregular : deriv alpha p ≠ 0)
    (hgeo : G.IsGeodesicOn alpha (Ioo a b))
    {W U V : Set AnnulusCoordinates} (hW : IsCompact W) (hpW : alpha p ∉ W)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc a b ∪ W) (hfV : frontier V = frontier U)
    (hK : IsCompact (closure U)) {gamma : ℝ → AnnulusCoordinates} {L u : ℝ}
    (hc : ContinuousOn gamma (Icc 0 L))
    (hconf : MapsTo gamma (Icc 0 L) (closure U))
    (hlip : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L,
      G.edist (gamma s) (gamma t) ≤ ENNReal.ofReal |s - t|)
    (hmin : ∀ c ∈ Icc 0 L, ∀ d ∈ Icc 0 L, c ≤ d →
      ∀ tau : ℝ → AnnulusCoordinates, ContinuousOn tau (Icc 0 1) →
        tau 0 = gamma c → tau 1 = gamma d → MapsTo tau (Icc 0 1) (closure U) →
        ENNReal.ofReal (d - c) ≤ m64IntrinsicCurveVariation G tau 0 1)
    (hu : u ∈ Ioo 0 L) (hpoint : gamma u = alpha p) :
    ∃ c : ℝ, c ≠ 0 ∧ gamma =ᶠ[𝓝 u] (fun t => alpha (c * t + (p - c * u))) ∧
      ∀ᶠ t in 𝓝 u, gamma t ∈ alpha '' Ioo a b := by
  have hfront : frontier (closure U) ⊆ alpha '' Icc a b ∪ W :=
    frontier_closure_subset.trans hfU.subset
  have hside : MapsTo alpha (Icc a b) (closure U) := by
    intro s hs
    apply frontier_subset_closure
    rw [hfU]
    exact Or.inl ⟨s, hs, rfl⟩
  obtain ⟨epsilon, hepsilon, hinterval, hgammaGeo, hgammaSmooth⟩ :=
    m64Intrinsic_constrained_minimizer_geodesic_side G hK.isClosed hW
      ha.continuous.continuousOn hinj hgeo hp hfront hside hpW hconf hlip hmin hu hpoint
  let T := u + epsilon / 2
  have huT : u < T := by dsimp only [T]; linarith
  have hTL : T ≤ L := by
    have hh := (hinterval (show u + epsilon ∈ Icc (u - epsilon) (u + epsilon) from
      ⟨by linarith, le_rfl⟩)).2
    dsimp only [T]
    linarith
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 L := fun t ht => ⟨ht.1, ht.2.trans hTL⟩
  have hshortGeo : G.IsGeodesicOn gamma (Ioo u T) := by
    intro t ht
    apply hgammaGeo t
    dsimp only [T] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨v, hv, _, c, hcne, hcv⟩ :=
    m64Intrinsic_constrained_minimizer_last_contact_tangent G ha hinj hp hregular
      hW hpW hU hV hdisj hfU hfV hK (hc.mono hsub) (fun t ht => hconf (hsub ht))
      (fun s hs t ht => hlip s (hsub hs) t (hsub ht))
      (fun s hs t ht => hmin s (hsub hs) t (hsub ht)) ⟨hu.1, huT⟩ hpoint hshortGeo
  have huJ : u ∈ Ioo (u - epsilon) (u + epsilon) := ⟨by linarith, by linarith⟩
  have hdgamma : HasDerivAt gamma (deriv gamma u) u :=
    (contMDiffAt_iff_contDiffAt.mp
      (hgammaSmooth.contMDiffAt (isOpen_Ioo.mem_nhds huJ))).differentiableAt
        (by simp) |>.hasDerivAt
  have hvelocity : deriv gamma u = c • deriv alpha p :=
    ((hdgamma.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi u)).symm.trans
      (hv.derivWithin (uniqueDiffWithinAt_Ioi u))).trans hcv
  let eta := fun t : ℝ => alpha (c * t + (p - c * u))
  have hparameter : c * u + (p - c * u) = p := by ring
  have hetaPoint : eta u = alpha p := by dsimp only [eta]; rw [hparameter]
  have hdalpha : HasDerivAt alpha (deriv alpha p) (c * u + (p - c * u)) := by
    rw [hparameter]
    exact (ha.differentiable (by simp) p).hasDerivAt
  have hdeta : HasDerivAt eta (c • deriv alpha p) u := by
    simpa only [eta, Function.comp_def, id_eq, mul_one] using!
      hdalpha.scomp u (((hasDerivAt_id u).const_mul c).add_const (p - c * u))
  have hgg : G.IsGeodesicOn gamma {u} := by
    intro t ht
    have heq : t = u := ht
    subst t
    exact hgammaGeo u huJ
  have heg : G.IsGeodesicOn eta {u} := by
    intro t ht
    have heq : t = u := ht
    subst t
    apply hgeo.comp_affine c (p - c * u)
    simpa only [mem_preimage, hparameter] using hp
  have hagree : gamma =ᶠ[𝓝 u] eta :=
    hgg.eq_nhds_of_initial_data heg (mem_singleton u) (gamma u) (by simp)
      (hpoint.trans hetaPoint.symm) (by
        simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using
          hvelocity.trans hdeta.deriv.symm)
  have hparamLimit : Tendsto (fun t : ℝ => c * t + (p - c * u)) (𝓝 u) (𝓝 p) := by
    have hcont : ContinuousAt (fun t : ℝ => c * t + (p - c * u)) u := by fun_prop
    simpa only [hparameter] using hcont.tendsto
  refine ⟨c, hcne, hagree, ?_⟩
  filter_upwards [hagree, hparamLimit.eventually (isOpen_Ioo.mem_nhds hp)] with t ht htp
  exact ⟨c * t + (p - c * u), htp, ht.symm⟩

end PoincareConjecture

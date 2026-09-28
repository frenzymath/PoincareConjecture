import PoincareConjecture.Proofs.M35.CapGeometry.SelectedRadialFieldBounds
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.Uniqueness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness Poincare.Analysis.Calculus

local notation "V" => EuclideanSpace ℝ (Fin 3)

noncomputable def selectedCoordinateRadialShape
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (coordinate : V → L.limit.sliceCarrier.carrier) (k : ℕ) (z : V) : ℝ :=
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
  let p := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ (coordinate z)).val
  axisWarpingSlope G ‖p‖ / axisWarpingRadius G ‖p‖

theorem blowupSequence_coordinate_radial_shape_jets_zero
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : V → L.limit.sliceCarrier.carrier)
      (_hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
      (_hi : ∀ z, (mfderiv (𝓡 3) (𝓡 3) coordinate z).IsInvertible)
      (g : RiemannianMetric 3 V)
      (_hg : g.euclideanCoefficients = (L.limit.flow.metric 0).pullbackCoefficients coordinate)
      (Ω : Set V) (_hΩ : IsOpen Ω) (_hcompact : IsCompact (closure Ω)),
      ∀ (m : ℕ) (K : Set V), IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn (fun k y => iteratedFDeriv ℝ m
          (selectedCoordinateRadialShape P E t x ht hR L coordinate k) y)
          (fun _ => 0) atTop K := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro coordinate hc hi g hg Ω hΩ hcompact
  let S := selectedCoordinateRadialShape P E t x ht hR L coordinate
  have hs : ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (S k) Ω := by
    filter_upwards [blowupSequence_coordinate_radial_domain P E t x ht hR hd L
      coordinate hc hi (closure Ω) hcompact] with k hk
    intro z hz
    have h := (hk z (subset_closure hz)).1.self_of_nhds
    have hf := contMDiffAt_iff_contDiffAt.mp h.1
    exact ((radial_shape_contDiffAt _ h.2.2).comp z hf).contDiffWithinAt
  have hb : LocallyEventuallyBoundedDerivatives Ω S := by
    intro K hK _hKΩ m
    obtain ⟨C, hC⟩ := blowupSequence_coordinate_radial_projected_jets_bounded
      P E t x ht hR hd L coordinate hc hi g hg K hK m
      (ContinuousLinearMap.snd ℝ V ℝ)
    exact ⟨C, hC⟩
  have hvalue (z : V) : Tendsto (fun k => S k z) atTop (𝓝 0) := by
    let G := L.limit.flow.metric 0
    let r := (G.edist L.limit.base (coordinate z)).toReal + 1
    have hz : coordinate z ∈ G.ball L.limit.base r := by
      apply (ENNReal.lt_ofReal_iff_toReal_lt (G.edist_ne_top _ _)).mpr
      exact lt_add_of_pos_right _ zero_lt_one
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    filter_upwards [blowupSequence_far_tip_radial_shape_on_limit_ball
      P E t x ht hR hd L r (epsilon / 2) (half_pos hepsilon)] with k hk
    have h := hk (coordinate z) hz
    change |S k z| ≤ epsilon / 2 at h
    simpa only [dist_zero_right, Real.norm_eq_abs] using
      h.trans_lt (half_lt_self hepsilon)
  intro m K hK hKΩ
  have hconv := tendstoUniformlyOn_iteratedFDeriv_of_eventually_smooth hΩ
    (fun z _ => hvalue z) hs hb m hK hKΩ
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_def, S] using hconv

end PoincareConjecture.M35.OrdinaryRealization

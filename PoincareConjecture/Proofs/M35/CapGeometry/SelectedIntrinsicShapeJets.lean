import PoincareConjecture.Proofs.M35.CapGeometry.SelectedRadialShapeConvergence
import PoincareConjecture.Proofs.M35.CapGeometry.IntrinsicShapeJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => StandardCapSpace

noncomputable def selectedCoordinateIntrinsicShapeDerivative
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (coordinate : V → L.limit.sliceCarrier.carrier) (k m : ℕ) : V → ℝ :=
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G : RiemannianMetric 3 V := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
  let hrot := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t (L.subsequence k)) (ht _)) Q hQ
  let hc := scaleSmoothMetric_complete (E.flow.metric (t (L.subsequence k)))
    (E.complete (t (L.subsequence k)) (ht _)) Q hQ
  let f : V → V := fun y => ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ (coordinate y)).val
  intrinsicShapeDerivativePullback G hrot hc f m

theorem blowupSequence_intrinsic_shape_jets_zero
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
      ∀ (m r : ℕ) (K : Set V), IsCompact K → K ⊆ Ω →
        ∀ (idx : ℕ → ℕ), Tendsto idx atTop atTop →
        ∀ (p : ℕ → V), (∀ k, p k ∈ K) →
          Tendsto (fun k => iteratedFDeriv ℝ r
            (selectedCoordinateIntrinsicShapeDerivative P E t x ht hR L
              coordinate (idx k) m) (p k)) atTop (𝓝 0) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate hc hi g hg Ω hΩ hcompact
  have hshape := blowupSequence_coordinate_radial_shape_jets_zero
    P E t x ht hR hd L coordinate hc hi g hg Ω hΩ hcompact
  intro m r K hK hKΩ idx hidx p hp
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence (idx k))
  have hQ k : 0 < Q k :=
    (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence (idx k))
  let G (k : ℕ) : RiemannianMetric 3 V :=
    M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence (idx k)))) (Q k) (hQ k)
  have hrot k := scaleSmoothMetric_rotation_invariant
    (E.rotation_invariant (t (L.subsequence (idx k))) (ht _)) (Q k) (hQ k)
  have hcomplete k := scaleSmoothMetric_complete
    (E.flow.metric (t (L.subsequence (idx k))))
    (E.complete (t (L.subsequence (idx k))) (ht _)) (Q k) (hQ k)
  let f (k : ℕ) (y : V) := ((L.embedding (idx k)).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos (idx k)).le, le_rfl⟩ (coordinate y)).val
  have hdomain : ∀ᶠ k in atTop, ∀ᶠ y in 𝓝 (p k),
      ContDiffAt ℝ ∞ (f k) y ∧ (fderiv ℝ (f k) y).IsInvertible ∧ f k y ≠ 0 := by
    filter_upwards [hidx.eventually (blowupSequence_coordinate_radial_domain
      P E t x ht hR hd L coordinate hc hi K hK)] with k hk
    have h := (hk (p k) (hp k)).1
    simpa only [contMDiffAt_iff_contDiffAt, mfderiv_eq_fderiv] using h
  have hfield (n : ℕ) : HasUniformJetBoundsAt n
      (fun k => pullback ℝ (f k) (radialUnitField (G k))) p := by
    intro j _hj
    obtain ⟨C, hC⟩ := blowupSequence_coordinate_radial_jets_bounded P E t x ht hR hd L
      coordinate hc hi g hg K hK j
    have hb : IsBoundedUnder (· ≤ ·) atTop
        (fun k => ‖iteratedFDeriv ℝ j (pullback ℝ (f k) (radialUnitField (G k))) (p k)‖) := by
      refine ⟨C, ?_⟩
      change ∀ᶠ k in atTop,
        ‖iteratedFDeriv ℝ j (pullback ℝ (f k) (radialUnitField (G k))) (p k)‖ ≤ C
      filter_upwards [hidx.eventually hC] with k hk
      exact hk (p k) (hp k)
    obtain ⟨B, hB⟩ := hb.bddAbove_range
    exact ⟨B, fun k => hB (mem_range_self k)⟩
  have hzero (n : ℕ) : Tendsto (fun k => iteratedFDeriv ℝ n
      (fun y => axisWarpingSlope (G k) ‖f k y‖ / axisWarpingRadius (G k) ‖f k y‖)
        (p k)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    filter_upwards [hidx.eventually (Metric.tendstoUniformlyOn_iff.mp
      (hshape n K hK hKΩ) epsilon hepsilon)] with k hk
    have h := hk (p k) (hp k)
    change dist 0 (iteratedFDeriv ℝ n
      (fun y => axisWarpingSlope (G k) ‖f k y‖ / axisWarpingRadius (G k) ‖f k y‖)
        (p k)) < epsilon at h
    simpa only [dist_comm] using h
  exact intrinsic_shape_derivative_jets_zero G hrot hcomplete f p hdomain hfield hzero m r

end PoincareConjecture.M35.OrdinaryRealization

import PoincareConjecture.Proofs.M30.Thm11_8.RawFiniteClosedLeftExtension
import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedClosedLeftRelatedNecks
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteLeftGlobalBound
import PoincareConjecture.Proofs.M30.Thm11_8.FiniteScalarPropagation

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.measurableSpace FlowCarrier.borelSpace FlowCarrier.secondCountable

theorem exists_raw_finite_scalar_bound_threshold
    (P : M30ControlledBlowupPredecessors.{u}) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ (S : GeneralizedBlowupSequence.{u}) (epsilon C kappa r0 mu : ℝ),
        epsilon ≤ epsilon0 → ∀ T0 : ℝ≥0∞,
      ∀ _H : M30LongBlowupControls S epsilon C kappa r0 mu T0,
      ∀ T : ℝ, 0 < T → ENNReal.ofReal T < T0 →
      ∀ G : GeneralizedBlowupConvergence S (Ioc (-T) 0),
        ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioc (-T) 0, ∀ x,
          (G.limit.flow.connection t).scalarCurvature x ≤ B := by
  obtain ⟨epsilonLeft, hleftPos, hleftSmall, hleft⟩ :=
    exists_raw_finite_closed_left_extension_threshold P
  obtain ⟨epsilonNeck, hneckPos, _hneckSmall, hneck⟩ :=
    exists_generalized_closed_left_related_neck_threshold.{u}
  obtain ⟨eta0, heta0, _hetaSmall, hbound⟩ :=
    exists_left_endpoint_scalar_bound_threshold P.m04
  let epsilon0 := min epsilonLeft (min epsilonNeck (eta0 / 4))
  refine ⟨epsilon0, lt_min hleftPos (lt_min hneckPos (by positivity)),
    (min_le_left _ _).trans hleftSmall, ?_⟩
  intro S epsilon C kappa r0 mu hepsilon T0 H T hT hTT0 G
  have hepsilonLeft : epsilon ≤ epsilonLeft :=
    hepsilon.trans (min_le_left _ _)
  have hepsilonNeck : epsilon ≤ epsilonNeck :=
    hepsilon.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsilonBound : 4 * epsilon ≤ eta0 := by
    have h := hepsilon.trans ((min_le_right _ _).trans (min_le_right _ _))
    change epsilon ≤ eta0 / 4 at h
    linarith
  obtain ⟨Fbar, hmetric, hcomplete, hsign, hlocal⟩ :=
    hleft S epsilon C kappa r0 mu hepsilonLeft T0 H T hT hTT0 G
  have hendpoint : -T ∈ Icc (-T) 0 := ⟨le_rfl, by linarith⟩
  have hrelated := hneck hT G epsilon C H.epsilon_pos hepsilonNeck
    (fun k => H.canonical (G.subsequence k)) Fbar hmetric (hcomplete (-T) hendpoint)
  obtain ⟨B, _hB, hscalar⟩ := hbound hT G Fbar
    (hcomplete (-T) hendpoint) (hsign (-T) hendpoint)
    (by
      intro A hA U hU
      obtain ⟨delta, hdelta, F, hF, hFsign⟩ := hlocal A hA U hU
      exact ⟨delta, hdelta, F, hF (-T) hendpoint, hFsign⟩)
    (4 * epsilon) (16 * max 1 C) (mul_pos (by norm_num) H.epsilon_pos)
    hepsilonBound (by
      intro x hx
      rcases hrelated x hx with ⟨N, hN, _hD, hratio⟩ | hcompact
      · refine Or.inl ⟨N, hN, ?_⟩
        have hlarge : (1 : ℝ) ≤ 16 * max 1 C := by
          nlinarith only [le_max_left (1 : ℝ) C]
        simpa only [max_eq_right hlarge] using hratio
      · exact Or.inr hcompact)
  apply exists_finite_scalar_bound_of_left_extension P.m04 hT
    H.toM30CommonBlowupControls G (fun t x => (Fbar.connection t).scalarCurvature x)
    (fun x => Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time
      P.m04 (Icc (-T) 0) Fbar x) ?_ hscalar
  intro t ht x
  have hreadout (g g' : RiemannianMetric 3 G.limit.carrier.carrier)
      (heq : g = g') (D : LeviCivitaData g) (D' : LeviCivitaData g') :
      D.scalarCurvature x = D'.scalarCurvature x := by
    subst g'
    exact D.scalarCurvature_eq D' x
  exact hreadout _ _ (hmetric t ht) (Fbar.connection t) (G.limit.flow.connection t)

end PoincareConjecture.M30

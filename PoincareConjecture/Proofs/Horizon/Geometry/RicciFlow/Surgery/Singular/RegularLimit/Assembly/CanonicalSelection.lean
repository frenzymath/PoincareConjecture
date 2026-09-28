import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Assembly.StaticTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.LateControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Persistence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Component.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Limit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open SingularRegularLimit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem frequently_reference_canonical_alternatives
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04)
    (hR : H.r₀⁻¹ ^ 2 < (H.terminalConnection P04).scalarCurvature x) :
    (∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : GeneralizedStrongNeck F t H.epsilon,
        N.center = H.reference.forward t ht x) ∨
    (∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : CapCertificate (F.metric t), N.epsilon = H.epsilon ∧
        N.cap_constant ≤ H.constant ∧ N.connection = F.connection t ∧
          H.reference.forward t ht x ∈ N.core) ∨
    (∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularCComponent (F.metric t) (F.connection t) H.constant,
        H.reference.forward t ht x ∈ N.carrier) ∨
    (∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
      ∃ N : SingularRoundComponent (F.metric t) H.epsilon,
        H.reference.forward t ht x ∈ N.carrier) := by
  rw [← frequently_or_distrib, ← frequently_or_distrib, ← frequently_or_distrib]
  obtain ⟨s, hsref, hsT, hcontrol⟩ := H.exists_late_reference_canonical_control P04 x hR
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsLT hsT] with t ht
  have hreference : t ∈ Ico H.reference.tMinus T := ⟨(hsref.trans ht.1).le, ht.2⟩
  rcases (hcontrol t hreference ht.1).2.2 with
    ⟨N, hcenter⟩ | ⟨N, hε, hC, hD, hx⟩ | ⟨N, hx⟩ | ⟨N, hx⟩
  · exact Or.inl ⟨hreference, N, hcenter⟩
  · exact Or.inr (Or.inl ⟨hreference, N, hε, hC, hD, hx⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hreference, N, hx⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hreference, N, hx⟩))

end PoincareConjecture.SingularTimeAssumptions

namespace PoincareConjecture.SingularRegularLimit

open RoundComparison

theorem exists_terminal_canonical_or_frequent_cap_threshold
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M), H.epsilon ≤ ε₀ →
        ∀ (hΩ : H.reference.regularLimitSet.Nonempty) (x : H.regularRegion P04),
          H.r₀⁻¹ ^ 2 < (H.terminalConnection P04).scalarCurvature x →
          TerminalCanonicalNeighborhood (H.nonemptyExtension P04 hΩ)
              ((H.terminalSliceHomeomorph P04).symm x)
              (terminalAccuracyFactor * H.epsilon) (2 * H.constant) ∨
          (∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
            ∃ N : CapCertificate (F.metric t), N.epsilon = H.epsilon ∧
              N.cap_constant ≤ H.constant ∧ N.connection = F.connection t ∧
                H.reference.forward t ht x ∈ N.core) := by
  obtain ⟨εN, hεN, hsmall, hneck⟩ := exists_terminal_strong_neck_persistence_threshold P04
  refine ⟨min εN roundComparisonThreshold, lt_min hεN roundComparisonThreshold_pos,
    (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H hε hΩ x hR
  have hpos : 0 < (H.terminalConnection P04).scalarCurvature x :=
    (sq_nonneg _).trans_lt hR
  rcases H.frequently_reference_canonical_alternatives P04 x hR with hN | hcap | hC | hround
  · left
    obtain ⟨N, hcenter⟩ := hneck H (hε.trans (min_le_left _ _)) hΩ x hpos (by
      intro s hs
      obtain ⟨t, ⟨ht, N, hcenter⟩, hlate⟩ :=
        (hN.and_eventually (Ioo_mem_nhdsLT (max_lt H.reference.tMinus_lt hs))).exists
      exact ⟨t, ⟨(le_max_left _ _).trans_lt hlate.1, hlate.2⟩,
        (le_max_right _ _).trans_lt hlate.1, N, hcenter⟩)
    exact GeneralizedCanonicalControl.neck N hcenter
  · exact Or.inr hcap
  · left
    obtain ⟨N, _, _, hx⟩ := H.exists_terminal_cComponent_of_frequently P04 x hC hpos
    obtain ⟨NT, hxT⟩ := SliceGeometry.exists_cComponent_of_eq
      (H.extendedSliceGeometry_terminal P04) ((H.terminalSliceHomeomorph P04).symm x)
      (show ∃ N : SingularCComponent (H.terminalMetric P04) (H.terminalConnection P04)
          (2 * H.constant), H.terminalSliceHomeomorph P04
            ((H.terminalSliceHomeomorph P04).symm x) ∈ N.carrier from
        ⟨N, by simpa only [Homeomorph.apply_symm_apply] using hx⟩)
    exact GeneralizedCanonicalControl.component NT hxT
  · left
    obtain ⟨N, _, hx⟩ := H.exists_terminal_roundComponent_of_frequently P04
      (hε.trans (min_le_right _ _)) x hround hpos
    obtain ⟨NT, hxT⟩ := SliceGeometry.exists_roundComponent_of_eq
      (H.extendedSliceGeometry_terminal P04) ((H.terminalSliceHomeomorph P04).symm x)
      (show ∃ N : SingularRoundComponent (H.terminalMetric P04)
          (terminalAccuracyFactor * H.epsilon),
          H.terminalSliceHomeomorph P04 ((H.terminalSliceHomeomorph P04).symm x)
            ∈ N.carrier from
        ⟨N, by simpa only [Homeomorph.apply_symm_apply] using hx⟩)
    exact GeneralizedCanonicalControl.round NT hxT

end PoincareConjecture.SingularRegularLimit

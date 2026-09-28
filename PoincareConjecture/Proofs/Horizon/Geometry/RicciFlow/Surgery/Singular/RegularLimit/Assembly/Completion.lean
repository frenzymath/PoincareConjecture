import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Assembly.CanonicalSelection
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Assembly.Conclusion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Assembly.SameCorePersistence
import PoincareConjecture.Statements.M31SingularRegularLimit



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

section

variable (P04 : RicciFlowCurvatureTheory.{u})

include P04

namespace SingularRegularLimit


theorem exists_terminal_cap_of_frequently_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M), H.epsilon ≤ ε₀ →
        ∀ x : H.regularRegion P04, 0 < (H.terminalConnection P04).scalarCurvature x →
          (∃ᶠ t in 𝓝[<] T, ∃ ht : t ∈ Ico H.reference.tMinus T,
            ∃ N : CapCertificate (F.metric t), N.epsilon = H.epsilon ∧
              N.cap_constant ≤ H.constant ∧ N.connection = F.connection t ∧
                H.reference.forward t ht x ∈ N.core) →
          ∃ N : CapCertificate (H.terminalMetric P04),
            N.epsilon = terminalAccuracyFactor * H.epsilon ∧
            N.cap_constant ≤ 2 * H.constant ∧ N.connection = H.terminalConnection P04 ∧
            x ∈ N.core := by
  obtain ⟨εP, hεP, hsmall, hcap⟩ := exists_terminal_same_core_cap_persistence_threshold P04
  obtain ⟨εC, hεC, _, hcapture⟩ := exists_neck_cap_compact_capture_threshold.{u}
  refine ⟨min εP εC, lt_min hεP hεC, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H hε x hx hfrequent
  obtain ⟨A, hA, hAreg, sA, _, hsAT, hcapture⟩ :=
    hcapture H P04 (hε.trans (min_le_right _ _)) x x.property
  let AΩ : Set (H.regularRegion P04) := Subtype.val ⁻¹' A
  have hAΩ : IsCompact AΩ := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hA
    intro y hy
    exact ⟨⟨y, hAreg hy⟩, rfl⟩
  have hlateA : ∀ᶠ t in 𝓝[<] T, t ∈ Ioo sA T := Ioo_mem_nhdsLT hsAT
  obtain ⟨t, ⟨ht, C, hCε, hCC, hCD, hxC⟩, hlate, hproduce⟩ :=
    (hfrequent.and_eventually (hlateA.and
      (hcap H (hε.trans (min_le_left _ _)) hAΩ x hx))).exists
  have hcaptured := (hcapture t ht hlate.1.le).2 C hCC hCD hxC
  have hCA : H.reference.inverse t ht '' C.carrier ⊆ Subtype.val '' AΩ := by
    intro y hy
    have hyA := hcaptured (subset_closure hy)
    exact ⟨⟨y, hAreg hyA⟩, hyA, rfl⟩
  exact hproduce ht C hCε hCC hCD hCA hxC


theorem exists_terminal_canonical_threshold :
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
            (terminalAccuracyFactor * H.epsilon) (2 * H.constant) := by
  obtain ⟨εS, hεS, hsmall, hselect⟩ := exists_terminal_canonical_or_frequent_cap_threshold P04
  obtain ⟨εC, hεC, _, hcap⟩ := exists_terminal_cap_of_frequently_threshold P04
  refine ⟨min εS εC, lt_min hεS hεC, (min_le_left _ _).trans hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H hε hΩ x hx
  rcases hselect H (hε.trans (min_le_left _ _)) hΩ x hx with hcanonical | hfrequent
  · exact hcanonical
  obtain ⟨C, hCε, hCC, hCD, hxC⟩ := hcap H (hε.trans (min_le_right _ _)) x
    ((sq_nonneg _).trans_lt hx) hfrequent
  obtain ⟨CT, hCTε, hCTC, hCTD, hxCT⟩ := SliceGeometry.exists_cap_of_eq
    (H.extendedSliceGeometry_terminal P04) ((H.terminalSliceHomeomorph P04).symm x)
    (show ∃ N : CapCertificate (H.terminalMetric P04),
      N.epsilon = terminalAccuracyFactor * H.epsilon ∧
      N.cap_constant ≤ 2 * H.constant ∧ N.connection = H.terminalConnection P04 ∧
      H.terminalSliceHomeomorph P04 ((H.terminalSliceHomeomorph P04).symm x) ∈ N.core from
        ⟨C, hCε, hCC, hCD, by simpa only [Homeomorph.apply_symm_apply] using hxC⟩)
  exact GeneralizedCanonicalControl.cap CT hCTε hCTC hCTD hxCT

end SingularRegularLimit



theorem horizon_m31SingularRegularLimit : RepairedSingularRegularLimitTheory.{u} := by
  obtain ⟨εL, hεL, _, hlimit⟩ :=
    SingularRegularLimit.exists_limit_conclusion_of_terminal_canonical_threshold P04
  obtain ⟨εC, hεC, _, hcanonical⟩ :=
    SingularRegularLimit.exists_terminal_canonical_threshold P04
  refine ⟨?_⟩
  intro A
  let ε₀ := min εL (min εC (A.epsilon₀ / terminalAccuracyFactor))
  have hε₀ : 0 < ε₀ := lt_min hεL
    (lt_min hεC (div_pos A.epsilon₀_pos terminalAccuracyFactor_pos))
  have hε₀A : terminalAccuracyFactor * ε₀ ≤ A.epsilon₀ := by
    have h := (min_le_right εL (min εC (A.epsilon₀ / terminalAccuracyFactor))).trans
      (min_le_right εC (A.epsilon₀ / terminalAccuracyFactor))
    have hh := (le_div_iff₀ terminalAccuracyFactor_pos).mp h
    simpa only [mul_comm] using hh
  refine ⟨ε₀, hε₀, hε₀A, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H hε
  apply hlimit A H (hε.trans (min_le_left _ _))
    ((mul_le_mul_of_nonneg_left hε terminalAccuracyFactor_pos.le).trans hε₀A)
  intro hΩ x hx
  have hx' : H.r₀⁻¹ ^ 2 < (H.terminalConnection P04).scalarCurvature
      (H.terminalSliceHomeomorph P04 x) := by
    rw [H.terminalSliceHomeomorph_scalar_pullback P04 x]
    exact hx
  have hcan := hcanonical H
    (hε.trans ((min_le_right _ _).trans (min_le_left _ _))) hΩ
    (H.terminalSliceHomeomorph P04 x) hx'
  simpa only [Homeomorph.symm_apply_apply] using hcan

end

end PoincareConjecture

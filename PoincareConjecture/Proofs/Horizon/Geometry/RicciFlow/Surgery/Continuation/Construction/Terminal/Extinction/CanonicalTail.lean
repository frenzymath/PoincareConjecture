import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.ScalarTail

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

theorem RepairedPreterminalSlab.scalar_identify {F : SurgeryFlowData.{u}} {T : ℝ}
    (S : RepairedPreterminalSlab F T) (t : Ico S.start T)
    (x : (F.slice S.start).carrier) :
    (S.flow.connection t.1).scalarCurvature x =
      (F.connection t.1).scalarCurvature (S.identify t x) := by
  exact (S.flow.connection t.1).scalarCurvature_eq_of_local_isometry
    (F.connection t.1) isOpen_univ (S.identify t).contMDiff.contMDiffOn
    (fun y _ v w => (S.metric_pullback t y v w).symm) (mem_univ x)

namespace RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B

theorem exists_canonical_tail (hempty : I.controlled_core = ∅) :
    ∃ s : ℝ, I.last_slab.start < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : (F.slice t).carrier,
        SurgeryCanonicalControl F t x F.parameters.epsilon F.parameters.C := by
  have hrT : 0 < F.parameters.r T := F.parameters.r_pos T I.terminal_pos.le
  have hinv : (F.parameters.r T)⁻¹ < I.rho⁻¹ :=
    (inv_lt_inv₀ hrT I.rho_pos).mpr I.rho_lt_r
  have hlevel : (F.parameters.r T)⁻¹ ^ 2 < I.rho⁻¹ ^ 2 := by
    have := inv_pos.mpr hrT
    nlinarith
  obtain ⟨s, hs, hsT, htail⟩ := B.preterminal_uniform_scalar_tail hempty _ hlevel
  obtain ⟨s', hss', hs'T⟩ := exists_between hsT
  refine ⟨s', hs.trans_lt hss', hs'T, ?_⟩
  intro t ht x
  have htpre : t ∈ Ico I.last_slab.start T := ⟨hs.trans (hss'.le.trans ht.1), ht.2⟩
  have htmem := I.last_slab.time_subset htpre
  have htzero : 0 ≤ t := F.time_domain_nonnegative htmem
  have hr : F.parameters.r T ≤ F.parameters.r t :=
    F.parameters.r_antitone htzero I.terminal_pos.le ht.2.le
  have hlevelt : (F.parameters.r t)⁻¹ ^ 2 ≤ (F.parameters.r T)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (F.parameters.r_pos t htzero).le)
      ((inv_le_inv₀ (F.parameters.r_pos t htzero) hrT).mpr hr) 2
  let e := I.last_slab.identify ⟨t, htpre⟩
  have hscalar := htail t ⟨hss'.le.trans ht.1, ht.2⟩ (e.symm x)
  rw [I.last_slab.scalar_identify ⟨t, htpre⟩] at hscalar
  change (F.parameters.r T)⁻¹ ^ 2 < (F.connection t).scalarCurvature (e (e.symm x))
    at hscalar
  rw [e.apply_symm_apply] at hscalar
  exact I.canonical t htmem x (hlevelt.trans hscalar.le)

end RepairedContinuationLimitBridge
end PoincareConjecture

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.ScalarTail
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.PreFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.CanonicalCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.RoundCurvature.PositiveSectional










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)

include B

theorem rebase_uniform_scalar_tail_off_open
    (D : Set (F.slice I.last_slab.start).carrier) (hD : IsOpen D)
    (hcore : I.controlled_core ⊆ D) (r : Ico I.last_slab.start T)
    (a : ℝ) (ha : a < I.rho⁻¹ ^ 2) :
    ∃ s : ℝ, r.1 < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : (F.slice r.1).carrier,
        x ∉ I.last_slab.identify r '' D →
          a < ((I.last_slab.rebaseFlow r).connection t).scalarCurvature x := by
  obtain ⟨s, hs, hsT, htail⟩ := B.preterminal_uniform_scalar_tail_off_open D hD hcore a ha
  obtain ⟨b, hb, hbT⟩ := exists_between (max_lt r.2.2 hsT)
  refine ⟨b, (le_max_left _ _).trans_lt hb, hbT, ?_⟩
  intro t ht x hx
  rw [I.last_slab.rebaseFlow_scalar]
  apply htail t ⟨((le_max_right _ _).trans_lt hb).le.trans ht.1, ht.2⟩
    ((I.last_slab.identify r).symm x)
  intro hin
  exact hx ⟨(I.last_slab.identify r).symm x, hin, (I.last_slab.identify r).apply_symm_apply x⟩

theorem exists_rebase_canonical_tail_off_open
    (D : Set (F.slice I.last_slab.start).carrier) (hD : IsOpen D)
    (hcore : I.controlled_core ⊆ D) (r : Ico I.last_slab.start T) :
    ∃ s : ℝ, r.1 < s ∧ s < T ∧
      ∀ t : Ico r.1 T, s ≤ t.1 → ∀ x : (F.slice r.1).carrier,
        x ∉ I.last_slab.identify r '' D →
          SurgeryCanonicalControl F t.1 (I.last_slab.rebaseIdentify r t x)
            F.parameters.epsilon F.parameters.C := by
  have hrT : 0 < F.parameters.r T := F.parameters.r_pos T I.terminal_pos.le
  have hinv : (F.parameters.r T)⁻¹ < I.rho⁻¹ :=
    (inv_lt_inv₀ hrT I.rho_pos).mpr I.rho_lt_r
  have hlevel : (F.parameters.r T)⁻¹ ^ 2 < I.rho⁻¹ ^ 2 := by
    have := inv_pos.mpr hrT
    nlinarith
  obtain ⟨s, hs, hsT, htail⟩ := B.rebase_uniform_scalar_tail_off_open D hD hcore r _ hlevel
  refine ⟨s, hs, hsT, ?_⟩
  intro t ht x hx
  have htmem := I.last_slab.time_subset ⟨r.2.1.trans t.2.1, t.2.2⟩
  have htzero : 0 ≤ t.1 := F.time_domain_nonnegative htmem
  have hr : F.parameters.r T ≤ F.parameters.r t.1 :=
    F.parameters.r_antitone htzero I.terminal_pos.le t.2.2.le
  have hlevelt : (F.parameters.r t.1)⁻¹ ^ 2 ≤ (F.parameters.r T)⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (F.parameters.r_pos t.1 htzero).le)
      ((inv_le_inv₀ (F.parameters.r_pos t.1 htzero) hrT).mpr hr) 2
  have hscalar := htail t.1 ⟨ht, t.2.2⟩ x hx
  have hident := ((I.last_slab.rebaseFlow r).connection t.1).scalarCurvature_eq_of_local_isometry
    (F.connection t.1) isOpen_univ (I.last_slab.rebaseIdentify r t).contMDiff.contMDiffOn
    (fun y _ v w => (I.last_slab.rebase_metric r t y v w).symm) (mem_univ x)
  rw [hident] at hscalar
  exact I.canonical t.1 htmem _ (hlevelt.trans hscalar.le)

theorem exists_rebase_disappearing_cover
    (D : Set (F.slice I.last_slab.start).carrier) (hD : IsOpen D)
    (hcore : I.controlled_core ⊆ D) (r : Ico I.last_slab.start T) :
    ∃ s : ℝ, r.1 < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : (F.slice r.1).carrier,
        x ∉ I.last_slab.identify r '' D →
          (∃ K : EpsilonNeck ((I.last_slab.rebaseFlow r).metric t),
            K.center = x ∧ K.epsilon = F.parameters.epsilon) ∨
          (∃ K : CapCertificate ((I.last_slab.rebaseFlow r).metric t),
            x ∈ K.core ∧ K.epsilon = F.parameters.epsilon ∧ K.cap_constant ≤ F.parameters.C) ∨
          (∃ U : Set (F.slice r.1).carrier, x ∈ U ∧ U = connectedComponent x ∧
            ∀ y ∈ U, ∀ v w : TangentSpace (𝓡 3) y,
              LeviCivitaData.IsOrthonormalPair ((I.last_slab.rebaseFlow r).metric t) y v w →
                0 < ((I.last_slab.rebaseFlow r).connection t).sectionalCurvature y v w) := by
  obtain ⟨s, hs, hsT, htail⟩ := B.exists_rebase_canonical_tail_off_open D hD hcore r
  refine ⟨s, hs, hsT, ?_⟩
  intro t ht x hx
  let q : Ico r.1 T := ⟨t, hs.le.trans ht.1, ht.2⟩
  have he : MetricHomothety ((I.last_slab.rebaseFlow r).metric t) (F.metric t)
      (I.last_slab.rebaseIdentify r q) 1 := by
    intro y v w
    simpa only [one_mul] using I.last_slab.rebase_metric r q y v w
  have hcover := SurgeryCanonicalControl.pullback_static_cover (F.slice r.1)
    ((I.last_slab.rebaseFlow r).metric t) ((I.last_slab.rebaseFlow r).connection t)
    (I.last_slab.rebaseIdentify r q) he x (htail q ht.1 x hx)
  rcases hcover with hneck | hcap | hpositive | ⟨K, hx⟩
  · exact Or.inl hneck
  · exact Or.inr (Or.inl hcap)
  · exact Or.inr (Or.inr hpositive)
  · refine Or.inr (Or.inr ⟨K.carrier, hx, ?_, ?_⟩)
    · rw [K.component_eq] at hx ⊢
      exact connectedComponent_eq hx
    · exact K.positive_sectional ((I.last_slab.rebaseFlow r).connection t)
        F.parameters.epsilon_le

end PoincareConjecture.RepairedContinuationLimitBridge

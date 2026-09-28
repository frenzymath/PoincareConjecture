import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitReference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.Disappearing








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RepairedContinuationLimitBridge

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  {L : RepairedSingularRegularLimitData H} {N : RepairedHornSelectionData H}
  {F : SurgeryFlowData.{u}} {I : RepairedContinuationInput F T}
  (B : RepairedContinuationLimitBridge H L N I)
  [Nonempty (N.limit.extension.extended.slice T).carrier]

def oldRetainedOpen (U : Opens (N.limit.extension.extended.slice T).carrier) :
    Opens (F.slice I.last_slab.start).carrier :=
  ⟨B.core_map ⁻¹' (N.limit.terminal_source '' (U : Set _)),
    (N.limit.terminal_source_openEmbedding.isOpenMap _ U.isOpen).preimage
      B.core_map_isOpenEmbedding.continuous⟩

theorem controlled_core_subset_oldRetainedOpen
    (U : Opens (N.limit.extension.extended.slice T).carrier)
    (hcore : {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2} ⊆ U) :
    I.controlled_core ⊆ B.oldRetainedOpen U := by
  intro x hx
  have h := B.core_map_image.subset (mem_image_of_mem _ hx)
  obtain ⟨_, z, hz, hscalar⟩ := h
  exact ⟨z, hcore hscalar, hz⟩

theorem reference_oldRetainedOpen_image
    (U : Opens (N.limit.extension.extended.slice T).carrier)
    (σ : Ico H.reference.tMinus T) :
    I.last_slab.identify (B.referenceRebaseTime σ) '' (B.oldRetainedOpen U : Set _) =
      (B.referenceLimitIdentify N.limit σ).inverse '' (U : Set _) := by
  apply Subset.antisymm
  · rintro _ ⟨x, ⟨z, hz, hzx⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    change (B.reference_identify σ).symm (N.limit.terminal_source z) = _
    rw [hzx, B.core_map_eq_reference_at σ x]
    exact (B.reference_identify σ).symm_apply_apply _
  · rintro _ ⟨z, hz, rfl⟩
    let x := (I.last_slab.identify (B.referenceRebaseTime σ)).symm
      ((B.reference_identify σ).symm (N.limit.terminal_source z))
    refine ⟨x, ?_, (I.last_slab.identify (B.referenceRebaseTime σ)).apply_symm_apply _⟩
    refine ⟨z, hz, ?_⟩
    rw [B.core_map_eq_reference_at σ x]
    simp only [x, referenceRebaseTime, Diffeomorph.apply_symm_apply]

theorem reference_uniform_scalar_tail_off_open
    (U : Opens (N.limit.extension.extended.slice T).carrier)
    (hcore : {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2} ⊆ U)
    (σ : Ico H.reference.tMinus T) (a : ℝ) (ha : a < I.rho⁻¹ ^ 2) :
    ∃ s : ℝ, σ.1 < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : (F.slice σ.1).carrier,
        x ∉ (B.referenceLimitIdentify N.limit σ).inverse '' (U : Set _) →
          a < ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).connection t).scalarCurvature x := by
  have h := B.rebase_uniform_scalar_tail_off_open (B.oldRetainedOpen U)
    (B.oldRetainedOpen U).isOpen (B.controlled_core_subset_oldRetainedOpen U hcore)
    (B.referenceRebaseTime σ) a ha
  rw [B.reference_oldRetainedOpen_image U σ] at h
  exact h

theorem exists_reference_disappearing_cover
    (U : Opens (N.limit.extension.extended.slice T).carrier)
    (hcore : {x | N.limit.terminal_scalar x ≤ I.rho⁻¹ ^ 2} ⊆ U)
    (σ : Ico H.reference.tMinus T) :
    ∃ s : ℝ, σ.1 < s ∧ s < T ∧
      ∀ t ∈ Ico s T, ∀ x : (F.slice σ.1).carrier,
        x ∉ (B.referenceLimitIdentify N.limit σ).inverse '' (U : Set _) →
          (∃ K : EpsilonNeck ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).metric t),
            K.center = x ∧ K.epsilon = F.parameters.epsilon) ∨
          (∃ K : CapCertificate ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).metric t),
            x ∈ K.core ∧ K.epsilon = F.parameters.epsilon ∧ K.cap_constant ≤ F.parameters.C) ∨
          (∃ V : Set (F.slice σ.1).carrier, x ∈ V ∧ V = connectedComponent x ∧
            ∀ y ∈ V, ∀ v w : TangentSpace (𝓡 3) y,
              LeviCivitaData.IsOrthonormalPair
                ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).metric t) y v w →
                  0 < ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).connection t).sectionalCurvature y v w) := by
  have h := B.exists_rebase_disappearing_cover (B.oldRetainedOpen U)
    (B.oldRetainedOpen U).isOpen (B.controlled_core_subset_oldRetainedOpen U hcore)
    (B.referenceRebaseTime σ)
  rw [B.reference_oldRetainedOpen_image U σ] at h
  exact h

end PoincareConjecture.RepairedContinuationLimitBridge

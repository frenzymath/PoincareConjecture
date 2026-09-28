import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.LimitSource
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Reference
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Extinction.Event.PreFlow




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

def referenceRebaseTime (σ : Ico H.reference.tMinus T) : Ico I.last_slab.start T :=
  ⟨σ.1, B.reference_start_lt.le.trans σ.2.1, σ.2.2⟩

def referenceLimitIdentify (Q : SingularLimitConclusion H)
    [Nonempty (Q.extension.extended.slice T).carrier] (σ : Ico H.reference.tMinus T) :
    SurgeryRegionEquivalence (F.slice σ.1) (Q.extension.extended.slice T)
      (B.reference_identify σ ⁻¹' H.reference.regularLimitSet) univ where
  map := Q.sourceInverse ∘ B.reference_identify σ
  inverse := (B.reference_identify σ).symm ∘ Q.terminal_source
  map_image := by
    apply eq_univ_of_forall
    intro z
    refine ⟨(B.reference_identify σ).symm (Q.terminal_source z), ?_, ?_⟩
    · simpa only [mem_preimage, Diffeomorph.apply_symm_apply] using Q.terminal_source_mem z
    · simp only [Function.comp_apply, Diffeomorph.apply_symm_apply, Q.sourceInverse_source]
  inverse_image := by
    ext x
    constructor
    · rintro ⟨z, _, rfl⟩
      simpa only [mem_preimage, Function.comp_apply, Diffeomorph.apply_symm_apply] using
        Q.terminal_source_mem z
    · intro hx
      refine ⟨Q.sourceInverse (B.reference_identify σ x), mem_univ _, ?_⟩
      simp only [Function.comp_apply, Q.source_sourceInverse hx, Diffeomorph.symm_apply_apply]
  left_inverse := by
    intro x hx
    simp only [Function.comp_apply, Q.source_sourceInverse hx, Diffeomorph.symm_apply_apply]
  right_inverse := by
    intro z _
    simp only [Function.comp_apply, Diffeomorph.apply_symm_apply, Q.sourceInverse_source]
  map_smooth := Q.sourceInverse_contMDiffOn.comp
    (B.reference_identify σ).contMDiff.contMDiffOn (fun _ hx => hx)
  inverse_smooth := ((B.reference_identify σ).symm.contMDiff.comp
    Q.terminal_source_smooth).contMDiffOn

theorem reference_regularLimit_open (Q : SingularLimitConclusion H)
    (σ : Ico H.reference.tMinus T) :
    IsOpen (B.reference_identify σ ⁻¹' H.reference.regularLimitSet) :=
  Q.regular_open.preimage (B.reference_identify σ).continuous

theorem reference_scalar_rebase (σ : Ico H.reference.tMinus T)
    (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T) (x : (F.slice σ.1).carrier) :
    H.reference.scalar t (B.reference_identify σ x) =
      ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).connection t).scalarCurvature x := by
  rw [I.last_slab.rebaseFlow_scalar]
  have hc := B.reference_scalar_core_map t ht
    ((I.last_slab.identify (B.referenceRebaseTime σ)).symm x)
  rw [B.core_map_eq_reference_at σ] at hc
  simpa only [referenceRebaseTime, Diffeomorph.apply_symm_apply] using hc

theorem core_map_metric (t : Ico H.reference.tMinus T)
    (x : (F.slice I.last_slab.start).carrier) (v w : TangentSpace (𝓡 3) x) :
    (H.reference.flow.metric t.1).inner (B.core_map x)
      (mfderiv (𝓡 3) (𝓡 3) B.core_map x v)
      (mfderiv (𝓡 3) (𝓡 3) B.core_map x w) =
        (I.last_slab.flow.metric t.1).inner x v w := by
  have heq : B.core_map = B.reference_identify t ∘
      I.last_slab.identify (B.referenceRebaseTime t) :=
    funext (B.core_map_eq_reference_at t)
  rw [heq, mfderiv_comp x
    ((B.reference_identify t).contMDiff.mdifferentiable (by simp) _)
    ((I.last_slab.identify (B.referenceRebaseTime t)).contMDiff.mdifferentiable (by simp) _)]
  exact B.reference_metric_pullback t x v w

theorem reference_metric_rebase (σ : Ico H.reference.tMinus T)
    (t : Ico H.reference.tMinus T) (x : (F.slice σ.1).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (H.reference.flow.metric t.1).inner (B.reference_identify σ x)
      (mfderiv (𝓡 3) (𝓡 3) (B.reference_identify σ) x v)
      (mfderiv (𝓡 3) (𝓡 3) (B.reference_identify σ) x w) =
        ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).metric t.1).inner x v w := by
  let e := I.last_slab.identify (B.referenceRebaseTime σ)
  have heq : B.core_map = B.reference_identify σ ∘ e :=
    funext (B.core_map_eq_reference_at σ)
  have hcore : ContMDiff (𝓡 3) (𝓡 3) ∞ B.core_map := by
    rw [heq]
    exact (B.reference_identify σ).contMDiff.comp e.contMDiff
  have heq' : B.core_map ∘ e.symm = B.reference_identify σ := by
    funext y
    simp only [heq, Function.comp_apply, Diffeomorph.apply_symm_apply]
  have hd := mfderiv_comp x (hcore.mdifferentiable (by simp) _)
    (e.symm.contMDiff.mdifferentiable (by simp) _)
  rw [heq'] at hd
  have hpoint : B.core_map (e.symm x) = B.reference_identify σ x :=
    congrFun heq' x
  rw [hd, I.last_slab.rebaseFlow_inner]
  change (H.reference.flow.metric t.1).inner (B.reference_identify σ x)
    (mfderiv (𝓡 3) (𝓡 3) B.core_map (e.symm x) (mfderiv (𝓡 3) (𝓡 3) e.symm x v))
    (mfderiv (𝓡 3) (𝓡 3) B.core_map (e.symm x) (mfderiv (𝓡 3) (𝓡 3) e.symm x w)) = _
  rw [← hpoint]
  exact B.core_map_metric t (e.symm x) _ _

theorem reference_regularLimit_eq (σ : Ico H.reference.tMinus T) :
    B.reference_identify σ ⁻¹' H.reference.regularLimitSet =
      {x | ∃ C : ℝ, ∀ t₀ : ℝ, t₀ < T → ∃ t ∈ Ico σ.1 T, t₀ < t ∧
        ((I.last_slab.rebaseFlow (B.referenceRebaseTime σ)).connection t).scalarCurvature x ≤ C} := by
  ext x
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, fun t₀ ht₀ => ?_⟩
    obtain ⟨t, ht, htr, hbound⟩ := hC (max t₀ σ.1) (max_lt ht₀ σ.2.2)
    refine ⟨t, ⟨((le_max_right _ _).trans_lt ht).le, htr.2⟩,
      (le_max_left _ _).trans_lt ht, ?_⟩
    rwa [← B.reference_scalar_rebase σ t htr]
  · rintro ⟨C, hC⟩
    refine ⟨C, fun t₀ ht₀ => ?_⟩
    obtain ⟨t, ht, hlt, hbound⟩ := hC t₀ ht₀
    have htr : t ∈ Ico H.reference.tMinus T := ⟨σ.2.1.trans ht.1, ht.2⟩
    refine ⟨t, hlt, htr, ?_⟩
    rwa [B.reference_scalar_rebase σ t htr]

end PoincareConjecture.RepairedContinuationLimitBridge

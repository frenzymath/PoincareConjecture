import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.InverseFunction.SmoothInverse








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ} {H : SingularTimeAssumptions G T M}
  (Q : SingularLimitConclusion H)

def referenceCarrier (_Q : SingularLimitConclusion H) : GeneralizedSliceCarrier.{u} where
  carrier := M
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

def regularOpen : Opens M := ⟨H.reference.regularLimitSet, Q.regular_open⟩

theorem terminal_source_mem (x : (Q.extension.extended.slice T).carrier) :
    Q.terminal_source x ∈ H.reference.regularLimitSet :=
  Q.terminal_source_image ▸ mem_range_self x

variable [Nonempty (Q.extension.extended.slice T).carrier]

def sourceInverse : M → (Q.extension.extended.slice T).carrier :=
  Function.invFun Q.terminal_source

@[simp] theorem sourceInverse_source (x : (Q.extension.extended.slice T).carrier) :
    Q.sourceInverse (Q.terminal_source x) = x :=
  Function.leftInverse_invFun Q.terminal_source_openEmbedding.injective x

theorem source_sourceInverse {x : M} (hx : x ∈ H.reference.regularLimitSet) :
    Q.terminal_source (Q.sourceInverse x) = x := by
  apply Function.invFun_eq
  have : x ∈ range Q.terminal_source := Q.terminal_source_image.symm ▸ hx
  exact this

theorem sourceInverse_contMDiffOn :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ Q.sourceInverse H.reference.regularLimitSet := by
  intro x hx
  obtain ⟨y, rfl⟩ := Q.terminal_source_image.symm ▸ hx
  exact (Poincare.contMDiffAt_of_local_left_inverse (Q.terminal_source_smooth y)
    (Q.terminal_source_regular y)
    (Eventually.of_forall Q.sourceInverse_source)).contMDiffWithinAt



def sourceDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) (Q.extension.extended.slice T).carrier Q.regularOpen ∞ where
  toFun x := ⟨Q.terminal_source x, Q.terminal_source_mem x⟩
  invFun x := Q.sourceInverse x.val
  left_inv := Q.sourceInverse_source
  right_inv x := Subtype.ext (Q.source_sourceInverse x.property)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff Q.regularOpen _).mp
    exact Q.terminal_source_smooth
  contMDiff_invFun := by
    intro x
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun x : Q.regularOpen => Q.sourceInverse x.val) x
    apply contMDiffAt_subtype_iff.mpr
    exact (Q.sourceInverse_contMDiffOn x.val x.property).contMDiffAt
      (Q.regular_open.mem_nhds x.property)



def sourceRegionEquivalence :
    SurgeryRegionEquivalence Q.referenceCarrier (Q.extension.extended.slice T)
      H.reference.regularLimitSet univ where
  map := Q.sourceInverse
  inverse := Q.terminal_source
  map_image := by
    apply eq_univ_of_forall
    intro x
    exact ⟨Q.terminal_source x, Q.terminal_source_mem x, Q.sourceInverse_source x⟩
  inverse_image := by
    simpa only [image_univ] using Q.terminal_source_image
  left_inverse := fun _ hx => Q.source_sourceInverse hx
  right_inverse := fun x _ => Q.sourceInverse_source x
  map_smooth := Q.sourceInverse_contMDiffOn
  inverse_smooth := Q.terminal_source_smooth.contMDiffOn

end PoincareConjecture.SingularLimitConclusion

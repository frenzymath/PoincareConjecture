import PoincareConjecture.Proofs.M47.SeedCylinderSource
import PoincareConjecture.Proofs.M11.OpenSubsetDiffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

variable {C : GeneralizedSliceCarrier.{u}}

noncomputable def neckOpenSourceCarrier (U : TopologicalSpace.Opens C.carrier) :
    GeneralizedSliceCarrier.{u} where
  carrier := U
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := inferInstance
  t3Space := inferInstance
  secondCountable := inferInstance

noncomputable def neckOpenSourceInclusion (U : TopologicalSpace.Opens C.carrier) (q : U) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) (neckOpenSourceCarrier U).carrier C.carrier ∞ := by
  let inclusion := U.openPartialHomeomorphSubtypeCoe ⟨q⟩
  have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inclusion.symm inclusion.target := by
    intro p hp
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U inclusion.symm inclusion.target p).mp
    apply contMDiffWithinAt_id.congr_of_mem _ hp
    intro x hx
    exact inclusion.right_inv hx
  exact {
    toPartialEquiv := inclusion.toPartialEquiv
    open_source := inclusion.open_source
    open_target := inclusion.open_target
    contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
    contMDiffOn_invFun := hi }

variable {F : SurgeryFlowData.{u}} {origin scale : ℝ} {I : Set ℝ}

noncomputable def neckOpenSourceCylinder (U : TopologicalSpace.Opens C.carrier) (q : U)
    (e : SurgeryFlowCylinder F C origin scale I U) :
    SurgeryFlowCylinder F (neckOpenSourceCarrier U) origin scale I univ :=
  seedCylinderSource e (neckOpenSourceInclusion U q) univ (Subset.refl _)
    (fun x _hx => x.property)

theorem neckOpenSourceCylinder_forward (U : TopologicalSpace.Opens C.carrier) (q : U)
    (e : SurgeryFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : U) :
    (neckOpenSourceCylinder U q e).forward s hs x = e.forward s hs x.val := rfl

theorem neckOpenSourceCylinder_pullbackInner (U : TopologicalSpace.Opens C.carrier) (q : U)
    (e : SurgeryFlowCylinder F C origin scale I U)
    (s : ℝ) (hs : s ∈ I) (x : U) (v w : TangentSpace (𝓡 3) x) :
    (neckOpenSourceCylinder U q e).pullbackInner s hs x v w =
      scale * (F.metric (origin + s / scale)).inner (e.forward s hs x.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x w) := rfl

end PoincareConjecture.Proofs.M47

import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

noncomputable def openSubtypePartialDiffeomorph (U : TopologicalSpace.Opens M)
    (hne : Nonempty U) : PartialDiffeomorph (𝓡 3) (𝓡 3) U M ∞ :=
  let e := U.openPartialHomeomorphSubtypeCoe hne
  { toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := (contMDiff_subtype_val (I := 𝓡 3) (U := U)).contMDiffOn
    contMDiffOn_invFun := by
      change ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target
      rw [show e.target = (U : Set M) from U.openPartialHomeomorphSubtypeCoe_target hne]
      exact openSubtypeInverse_contMDiffOn U hne }

@[simp] theorem openSubtypePartialDiffeomorph_source
    (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
    (openSubtypePartialDiffeomorph U hne).source = univ :=
  U.openPartialHomeomorphSubtypeCoe_source hne

@[simp] theorem openSubtypePartialDiffeomorph_target
    (U : TopologicalSpace.Opens M) (hne : Nonempty U) :
    (openSubtypePartialDiffeomorph U hne).target = (U : Set M) :=
  U.openPartialHomeomorphSubtypeCoe_target hne

@[simp] theorem openSubtypePartialDiffeomorph_apply
    (U : TopologicalSpace.Opens M) (hne : Nonempty U) (x : U) :
    openSubtypePartialDiffeomorph U hne x = x.val := rfl

end PoincareConjecture.M28

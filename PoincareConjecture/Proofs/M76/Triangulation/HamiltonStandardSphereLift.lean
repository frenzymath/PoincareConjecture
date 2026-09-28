import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel
import PoincareConjecture.Proofs.M76.Mathlib.CoveringProduct
import PoincareConjecture.Proofs.M02.SphereConnectivity
import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

private theorem cubeSphere_lifting_connectedness :
    SimplyConnectedSpace (sphere (0 : Fin 3 → ℝ) 1) ∧
      LocallyPathConnectedSpace (sphere (0 : Fin 3 → ℝ) 1) := by
  let c : (Fin 3 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph c
  let : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    PoincareConjecture.Proofs.M02.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : LocallyPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (H := EuclideanSpace ℝ (Fin 2))
      (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  exact ⟨H.toHomotopyEquiv.simplyConnectedSpace,
    H.isOpenEmbedding.locallyPathConnectedSpace⟩

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
  {α : Type*}
  {d : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
  {S : Set (LatticeHandleAmbient ι κ L)}

omit [Fintype ι] [Fintype κ] in



theorem ChartwisePLSphere.exists_standard_lattice_lift
    (s : ChartwisePLSphere d S) :
    ∃ l : C(sphere (0 : Fin 3 → ℝ) 1, (ι → ℝ) × (κ → ℝ)),
      Function.Injective l ∧
      ∀ x, ((l x).1, QuotientAddGroup.mk (l x).2) =
        (s.parametrization x : LatticeHandleAmbient ι κ L) := by
  classical
  let : SimplyConnectedSpace (sphere (0 : Fin 3 → ℝ) 1) :=
    cubeSphere_lifting_connectedness.1
  let : LocallyPathConnectedSpace (sphere (0 : Fin 3 → ℝ) 1) :=
    cubeSphere_lifting_connectedness.2
  let q : (κ → ℝ) → ((κ → ℝ) ⧸ L.toAddSubgroup) := QuotientAddGroup.mk
  have hq : IsCoveringMap q :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap
  let p : ((ι → ℝ) × (κ → ℝ)) → LatticeHandleAmbient ι κ L := Prod.map id q
  have hp : IsCoveringMap p := hq.id_prod
  let f : C(sphere (0 : Fin 3 → ℝ) 1, LatticeHandleAmbient ι κ L) :=
    ⟨fun x => (s.parametrization x : LatticeHandleAmbient ι κ L),
      continuous_subtype_val.comp s.parametrization.continuous⟩
  let x0 : sphere (0 : Fin 3 → ℝ) 1 := Classical.choice inferInstance
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (f x0).2
  have hbase : p ((f x0).1, z) = f x0 := Prod.ext rfl hz
  obtain ⟨l, ⟨_, hl⟩, _⟩ := hp.existsUnique_continuousMap_lifts f x0 ((f x0).1, z) hbase
  have hpoint (x : sphere (0 : Fin 3 → ℝ) 1) : p (l x) = f x := congrFun hl x
  refine ⟨l, ?_, fun x => hpoint x⟩
  intro x y hxy
  apply s.parametrization.injective
  apply Subtype.ext
  exact (hpoint x).symm.trans ((congrArg p hxy).trans (hpoint y))

end PoincareConjecture.M76

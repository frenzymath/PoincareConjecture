import PoincareConjecture.Proofs.M76.Brown.NormalBundleSection
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M02.SphereConnectivity
import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)

abbrev NormalPlane := {j : Fin 3 // j ≠ 0} → ℝ

noncomputable def flatteningAtlas {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    BrownCollar.FlatteningAtlas NormalPlane S S := by
  classical
  let A : S → OpenPartialHomeomorph V3 V3 := fun x =>
    (hS.flatten x.val x.property).choose
  have hA (x : S) : (x : V3) ∈ (A x).source ∧
      ∀ y ∈ (A x).source, y ∈ S ↔ A x y 0 = 0 :=
    (hS.flatten x.val x.property).choose_spec
  let J : V3 ≃ₜ NormalPlane × ℝ :=
    (Homeomorph.piSplitAt (0 : Fin 3) (fun _ : Fin 3 => ℝ)).trans
      (Homeomorph.prodComm ℝ NormalPlane)
  exact
    { chart := fun i => (A i).transHomeomorph J
      pair := fun i y hy => (hA i).2 y hy
      indexAt := id
      mem_source_at := fun x => (hA x).1 }

theorem lifting_connectedness {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    SimplyConnectedSpace S ∧ LocallyPathConnectedSpace S := by
  let c : V3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := hS.parametrization.symm.trans
    (PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph c)
  let : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    PoincareConjecture.Proofs.M02.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : LocallyPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (H := EuclideanSpace ℝ (Fin 2))
      (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  exact ⟨H.toHomotopyEquiv.simplyConnectedSpace,
    H.isOpenEmbedding.locallyPathConnectedSpace⟩

theorem exists_coherent_normal_units {S : Set V3} (hS : LocallyFlatTopologicalSphere S) :
    ∃ a : S → S → SignTypeˣ,
      (∀ i, ContinuousOn (a i) (hS.flatteningAtlas.baseSet i)) ∧
      ∀ i j x, x ∈ hS.flatteningAtlas.baseSet i ∩ hS.flatteningAtlas.baseSet j →
        a j x = hS.flatteningAtlas.transitionUnit i j x * a i x := by
  let : SimplyConnectedSpace S := hS.lifting_connectedness.1
  let : LocallyPathConnectedSpace S := hS.lifting_connectedness.2
  obtain ⟨x0, hx0⟩ :=
    (show (sphere (0 : V3) 1).Nonempty from NormedSpace.sphere_nonempty.mpr zero_le_one)
  let : Nonempty S := ⟨hS.parametrization ⟨x0, hx0⟩⟩
  exact hS.flatteningAtlas.exists_coherent_normal_units

end PoincareConjecture.M76.LocallyFlatTopologicalSphere

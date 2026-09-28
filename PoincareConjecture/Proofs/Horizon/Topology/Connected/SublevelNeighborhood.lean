import PoincareConjecture.Proofs.Horizon.Topology.Connected.SublevelEndpoint



noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace Poincare.Topology
variable {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]



theorem exists_open_neighborhood_sublevel_component
    {f : X → ℝ} (hf : Continuous f) (p : X) (a : ℝ)
    (hlocal : ∀ x, f x = a → HasConnectedLowerSide f univ a x) :
    ∃ U : Set X, IsOpen U ∧
      closure (connectedComponentIn (f ⁻¹' Iio a) p) ⊆ U ∧
      U ∩ f ⁻¹' Iic a ⊆ closure (connectedComponentIn (f ⁻¹' Iio a) p) := by
  let C := connectedComponentIn (f ⁻¹' Iio a) p
  let K := closure C
  have hKsub : K ⊆ f ⁻¹' Iic a :=
    closure_minimal ((connectedComponentIn_subset _ _).trans
      (preimage_mono Iio_subset_Iic_self)) (isClosed_Iic.preimage hf)
  have hside (x : X) (hx : x ∈ K) (V : Set X) (hV : IsOpen V) (hxV : x ∈ V)
      (hconn : IsPreconnected (V ∩ f ⁻¹' Iio a)) : V ∩ f ⁻¹' Iio a ⊆ C := by
    obtain ⟨z, hzV, hzC⟩ := mem_closure_iff.mp hx V hV hxV
    have hz : z ∈ V ∩ f ⁻¹' Iio a := ⟨hzV, connectedComponentIn_subset _ _ hzC⟩
    have hs := hconn.subset_connectedComponentIn hz inter_subset_right
    rwa [← connectedComponentIn_eq hzC] at hs
  have hnbhd (x : X) (hx : x ∈ K) :
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ∩ f ⁻¹' Iic a ⊆ K := by
    by_cases hxa : f x < a
    · let V := connectedComponentIn (f ⁻¹' Iio a) x
      have hV : IsOpen V := (isOpen_Iio.preimage hf).connectedComponentIn
      have hxV : x ∈ V := mem_connectedComponentIn hxa
      have heq : V ∩ f ⁻¹' Iio a = V := inter_eq_left.mpr (connectedComponentIn_subset _ _)
      have hs := hside x hx V hV hxV
        (by rw [heq]; exact isPreconnected_connectedComponentIn)
      refine ⟨V, hV, hxV, fun y hy => subset_closure ?_⟩
      exact hs ⟨hy.1, connectedComponentIn_subset _ _ hy.1⟩
    · have hxa : f x = a := le_antisymm (hKsub hx) (le_of_not_gt hxa)
      obtain ⟨V, hV, hxV, _, hconn, hdense⟩ := hlocal x hxa
      exact ⟨V, hV, hxV, fun y hy =>
        closure_mono (hside x hx V hV hxV hconn) (hdense hy)⟩
  choose V hV hxV hVK using hnbhd
  refine ⟨⋃ x ∈ K, V x ‹x ∈ K›, isOpen_iUnion fun x => isOpen_iUnion (hV x), ?_, ?_⟩
  · intro x hx
    exact mem_iUnion₂.mpr ⟨x, hx, hxV x hx⟩
  · rintro y ⟨hy, hya⟩
    obtain ⟨x, hx, hyV⟩ := mem_iUnion₂.mp hy
    exact hVK x hx ⟨hyV, hya⟩

end Poincare.Topology

import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence









set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.boundary_contact_nonempty
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    (D ∩ frontier (latticeHandleDomain ι κ L)).Nonempty := by
  rcases b.position with ⟨hzero,_⟩ | ⟨_,_,_,_,_,hmark⟩
  · omega
  let : Nonempty ι := Fintype.card_pos_iff.mp hpos
  obtain ⟨x,hx⟩ := (NormedSpace.sphere_nonempty (E := ι → ℝ) (x := 0)).mpr
    (show (0 : ℝ) ≤ 1 by norm_num)
  rw [hmark]
  refine ⟨hamiltonMarkedProjection ι κ L (x,0),(x,0),⟨hx,?_⟩,rfl⟩
  exact mem_closedBall_self (by norm_num)

theorem HamiltonMarkedProtectedBall.subset_residual_exterior
    {ι κ α ν : Type*} [Fintype ι] [Fintype κ] [Finite ν]
    {L : Submodule ℤ (κ → ℝ)}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι)
    (Q : ν → Set (LatticeHandleAmbient ι κ L))
    (hQ : ∀ i, IsClosed (Q i))
    (hinside : ∀ i, Q i ⊆ interior (latticeHandleDomain ι κ L))
    (havoid : ∀ i, Disjoint D (frontier (Q i))) :
    IsOpen (⋃ i, Q i)ᶜ ∧
      D ∪ frontier (latticeHandleDomain ι κ L) ⊆ (⋃ i, Q i)ᶜ := by
  have hc : IsConnected (closedBall (0 : V3) 1) :=
    (convex_closedBall _ _).isConnected ⟨0,mem_closedBall_self zero_le_one⟩
  let : ConnectedSpace (closedBall (0 : V3) 1) := isConnected_iff_connectedSpace.mp hc
  let : ConnectedSpace D := b.ball.parametrization.connectedSpace_iff.mp inferInstance
  have hD : IsConnected D := isConnected_iff_connectedSpace.mpr inferInstance
  obtain ⟨p,hpD,hpR⟩ := b.boundary_contact_nonempty hpos
  have hDout (i : ν) : D ⊆ (Q i)ᶜ := by
    apply hD.isPreconnected.m76_subset_of_disjoint_frontier (hQ i).isOpen_compl
    · simpa only [frontier_compl] using (havoid i).symm
    · exact ⟨p,hpD,fun hp => hpR.2 (hinside i hp)⟩
  refine ⟨(isClosed_iUnion_of_finite hQ).isOpen_compl,?_⟩
  intro x hx hxi
  obtain ⟨i,hi⟩ := mem_iUnion.mp hxi
  rcases hx with hxD | hxR
  · exact hDout i hxD hi
  · exact hxR.2 (hinside i hi)

end PoincareConjecture.M76

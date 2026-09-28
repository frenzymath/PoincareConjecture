import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.PuncturedSphereModelBoundary
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.GlobalExteriorDiskProduct
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.Topology
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Complement.ProperDiskSelectedHole










set_option autoImplicit false
open Set Metric Geometry

namespace Set

theorem IsConnected.exists_eq_label_of_closed_partition
    {X κ : Type*} [TopologicalSpace X] [Finite κ] {B T : Set X}
    (hB : IsConnected B) (hBclosed : IsClosed B) (hTclosed : IsClosed T)
    (hBT : Disjoint B T) (S : κ → Set X)
    (hS : ∀ i, IsConnected (S i)) (hSclosed : ∀ i, IsClosed (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hcover : B ∪ T = ⋃ i, S i) :
    ∃ i, S i = B ∧ (∀ j, j ≠ i → Disjoint (S j) B) ∧
      T = ⋃ j : {j : κ // j ≠ i}, S j := by
  classical
  obtain ⟨i, hBi, _⟩ := hB.exists_unique_subset_finite_disjoint_closed
    S hSclosed hSdis (subset_union_left.trans hcover.subset)
  have hSiB : S i ⊆ B := by
    have h := isPreconnected_iff_subset_of_disjoint_closed.mp (hS i).isPreconnected
      B T hBclosed hTclosed ((subset_iUnion S i).trans hcover.symm.subset)
      (by rw [hBT.inter_eq, inter_empty])
    rcases h with h | h
    · exact h
    · obtain ⟨x, hx⟩ := hB.nonempty
      exact False.elim (disjoint_left.mp hBT hx (h (hBi hx)))
  have heq : S i = B := Subset.antisymm hSiB hBi
  have hother (j : κ) (hji : j ≠ i) : Disjoint (S j) B := heq ▸ hSdis hji
  refine ⟨i, heq, hother, ?_⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover.subset (Or.inr hx))
    have hji : j ≠ i := by
      rintro rfl
      exact disjoint_left.mp hBT (heq ▸ hj) hx
    exact mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have h := hcover.symm.subset (mem_iUnion.mpr ⟨j, hj⟩)
    exact h.resolve_left (fun hB => disjoint_left.mp (hother j j.property) hj hB)

end Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_selected_component_boundary_label_of_subset
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X}
    (hR : IsCompact R) (hRPL : PLDomain e R) (hKPL : PLDomain e K)
    (hKR : K ⊆ interior R)
    (B : Bool → Set X) (sB : ∀ b, ChartwisePLSphere e (B b))
    (hBdis : Disjoint (B false) (B true)) (hKfront : frontier K = B false ∪ B true)
    (owner : Bool) {x : X}
    (hBC : B owner ⊆ _root_.connectedComponentIn (R ∩ (interior K)ᶜ) x)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hSdis : Pairwise fun i j => Disjoint (S i) (S j))
    (hfront : frontier (_root_.connectedComponentIn (R ∩ (interior K)ᶜ) x) = ⋃ i, S i) :
    ∃ i, S i = B owner ∧ (∀ j, j ≠ i → Disjoint (S j) (B owner)) ∧
      ((_root_.connectedComponentIn (R ∩ (interior K)ᶜ) x) ∩ frontier R) ∪
        ((_root_.connectedComponentIn (R ∩ (interior K)ᶜ) x) ∩ B (!owner)) =
          ⋃ j : {j : κ // j ≠ i}, S j := by
  let L := R ∩ (interior K)ᶜ
  let C := _root_.connectedComponentIn L x
  obtain ⟨hL, hLPL, _, _, hLfront⟩ := hRPL.interior_removal_geometry hR hKPL hKR
  have hBK (b : Bool) : B b ⊆ frontier K := by
    rw [hKfront]
    cases b
    · exact subset_union_left
    · exact subset_union_right
  have hBL (b : Bool) : B b ⊆ L := by
    intro y hy
    have hyK := hBK b hy
    exact ⟨interior_subset (hKR (hKPL.closed.frontier_subset hyK)),hyK.2⟩
  have hxL : x ∈ L := connectedComponentIn_nonempty_iff.mp
    ((sB owner).isConnected.nonempty.mono hBC)
  have hCcompact : IsCompact C := isCompact_connectedComponentIn_of_mem hL hxL
  let : LocallyPathConnectedSpace L := hLPL.locallyPathConnectedSpace
  obtain ⟨U, hU, hCU⟩ := exists_open_inter_of_relative_open (connectedComponentIn_subset L x)
    (isOpen_preimage_connectedComponentIn hxL)
  have hCfront : frontier C = C ∩ frontier L :=
    frontier_eq_inter_of_eq_inter_open hL.isClosed hCcompact.isClosed hU hCU
  let T := (C ∩ frontier R) ∪ (C ∩ B (!owner))
  have hcover : B owner ∪ T = frontier C := by
    rw [hCfront,hLfront,hKfront]
    dsimp only [T]
    ext y
    have hb : y ∈ B owner → y ∈ C := fun hy => hBC hy
    cases owner <;>
      simp only [Bool.not_false, Bool.not_true, mem_union, mem_inter_iff] at * <;> tauto
  have hBT : Disjoint (B owner) T := by
    apply disjoint_left.mpr
    intro y hyB hyT
    rcases hyT with hyR | hyother
    · exact hyR.2.2 (hKR (hKPL.closed.frontier_subset (hBK owner hyB)))
    · cases owner
      · exact disjoint_left.mp hBdis hyB hyother.2
      · exact disjoint_left.mp hBdis hyother.2 hyB
  exact (sB owner).isConnected.exists_eq_label_of_closed_partition
    (sB owner).isCompact.isClosed
    ((hCcompact.isClosed.inter isClosed_frontier).union
      (hCcompact.isClosed.inter (sB (!owner)).isCompact.isClosed))
    hBT S (fun i => (sS i).isConnected) (fun i => (sS i).isCompact.isClosed)
    hSdis (hcover.trans hfront)

end PoincareConjecture.M76

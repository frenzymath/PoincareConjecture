import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalConfinedSphereBall
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.AnnulusSides

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_innermost_original_sphere_ball
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (S : κ → Set X) (sS : ∀ i, ChartwisePLSphere e (S i))
    (hdis : Pairwise fun i j => Disjoint (S i) (S j))
    {B R : Set X} (b : ChartwisePLBall e B R)
    (hinside : ∃ i, S i ⊆ interior B) :
    ∃ i D, D ⊆ interior B ∧ Nonempty (ChartwisePLBall e D (S i)) ∧
      Disjoint (interior D) (⋃ j, S j) ∧
      (interior D).Nonempty ∧
      ∀ x ∈ interior D,
        connectedComponentIn (⋃ j, S j)ᶜ x = interior D ∧
        closure (connectedComponentIn (⋃ j, S j)ᶜ x) = D := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  let inside (D : Set X) := Finset.univ.filter (fun i => S i ⊆ interior D)
  have hconn (i : κ) : IsConnected (S i) := isConnected_iff_connectedSpace.mpr
    ((sS i).parametrization.connectedSpace_iff.mp (isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by simp) (0 : V3) zero_le_one)))
  have hex : ∃ m : ℕ, ∃ i D, Nonempty (ChartwisePLBall e D (S i)) ∧
      D ⊆ interior B ∧ (inside D).card = m := by
    obtain ⟨i,hi⟩ := hinside
    obtain ⟨D,hDB,hD⟩ := (sS i).exists_original_confined_ball he b hi
    exact ⟨(inside D).card,i,D,hD,hDB,rfl⟩
  obtain ⟨i,D,⟨d⟩,hDB,hm⟩ := Nat.find_spec hex
  have hmiss : Disjoint (interior D) (⋃ j, S j) := by
    apply disjoint_left.mpr
    intro x hxD hxS
    obtain ⟨j,hxj⟩ := mem_iUnion.mp hxS
    have hji : j ≠ i := by
      rintro rfl
      exact (d.interior_eq_sdiff.subset hxD).2 hxj
    have hjD : S j ⊆ interior D := (hconn j).isPreconnected.subset_interior_of_avoids_frontier
      (by rw [d.frontier_eq]; exact hdis hji) ⟨x,hxj,hxD⟩
    obtain ⟨D',hD'D,⟨d'⟩⟩ := (sS j).exists_original_confined_ball he d hjD
    have hsub : inside D' ⊆ inside D := by
      intro k hk
      simp only [inside,Finset.mem_filter,Finset.mem_univ,true_and] at hk ⊢
      exact hk.trans (interior_subset.trans hD'D)
    have hjold : j ∈ inside D := by simp [inside,hjD]
    have hjnew : j ∉ inside D' := by
      simp only [inside,Finset.mem_filter,Finset.mem_univ,true_and]
      intro h
      obtain ⟨y,hy⟩ := (hconn j).nonempty
      exact (d'.interior_eq_sdiff.subset (h hy)).2 hy
    have hlt : (inside D').card < (inside D).card := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,fun h => hjnew (h.symm ▸ hjold)⟩)
    have hmin := Nat.find_min' hex
      (show ∃ k E, Nonempty (ChartwisePLBall e E (S k)) ∧ E ⊆ interior B ∧
        (inside E).card = (inside D').card from
        ⟨j,D',⟨d'⟩,hD'D.trans (interior_subset.trans hDB),rfl⟩)
    omega
  have hDconn := d.isConnected_interior
  refine ⟨i,D,hDB,⟨d⟩,hmiss,hDconn.nonempty,?_⟩
  intro x hx
  have hxout : x ∈ (⋃ j, S j)ᶜ := fun h => disjoint_left.mp hmiss hx h
  have hcc := isConnected_connectedComponentIn_iff.mpr hxout
  have hccfront : Disjoint (connectedComponentIn (⋃ j, S j)ᶜ x) (frontier D) := by
    rw [d.frontier_eq]
    apply disjoint_left.mpr
    intro y hy hyS
    exact (connectedComponentIn_subset _ _ hy) (mem_iUnion.mpr ⟨i,hyS⟩)
  have hccD : connectedComponentIn (⋃ j, S j)ᶜ x ⊆ interior D :=
    hcc.isPreconnected.subset_interior_of_avoids_frontier hccfront
      ⟨x,mem_connectedComponentIn hxout,hx⟩
  have hEq : connectedComponentIn (⋃ j, S j)ᶜ x = interior D :=
    Subset.antisymm hccD (hDconn.isPreconnected.subset_connectedComponentIn hx
      (fun y hy h => disjoint_left.mp hmiss hy h))
  exact ⟨hEq,by rw [hEq,d.closure_interior]⟩

end PoincareConjecture.M76

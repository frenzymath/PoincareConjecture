import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryBumping
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainIntersection









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

variable {X : Type*} [TopologicalSpace X] [T2Space X]

theorem isConnected_sdiff_of_connected_frontier
    {R U : Set X} (hR : IsCompact R) (hRc : IsConnected R)
    (hU : IsOpen U) (hcl : closure U ⊆ R) (hf : IsConnected (frontier U)) :
    IsConnected (R \ U) := by
  have hfc : frontier U ⊆ R \ U := by
    intro x hx
    exact ⟨hcl hx.1, fun h => hx.2 (hU.interior_eq.symm ▸ h)⟩
  obtain ⟨p,hp⟩ := hf.nonempty
  have hUne : U.Nonempty := by
    by_contra h
    have heq : U = ∅ := not_nonempty_iff_eq_empty.mp h
    simp only [heq,frontier_empty,mem_empty_iff_false] at hp
  obtain ⟨q,hq⟩ := hUne
  have hmeet : (R ∩ U).Nonempty := ⟨q,hcl (subset_closure hq),hq⟩
  have hall : R \ U ⊆ connectedComponentIn (R \ U) p := by
    intro x hx
    obtain ⟨y,hy,hyf⟩ :=
      Poincare.Topology.connectedComponentIn_diff_inter_frontier_nonempty hR hRc hU hmeet hx
    have hfront := hf.isPreconnected.subset_connectedComponentIn hyf hfc
    have hpcomp : p ∈ connectedComponentIn (R \ U) x := by
      rw [connectedComponentIn_eq hy]
      exact hfront hp
    rw [← connectedComponentIn_eq hpcomp]
    exact mem_connectedComponentIn hx
  have heq : connectedComponentIn (R \ U) p = R \ U :=
    (connectedComponentIn_subset _ _).antisymm hall
  rw [←heq]
  exact isConnected_connectedComponentIn_iff.mpr (hfc hp)

omit [T2Space X] in
theorem frontier_sdiff_open_of_closure_subset_interior
    {R U : Set X} (hR : IsClosed R) (hU : IsOpen U)
    (hcl : closure U ⊆ interior R) :
    frontier (R \ U) = frontier R ∪ frontier U := by
  change frontier (R ∩ Uᶜ) = _
  rw [frontier_inter_eq_of_closed hR hU.isClosed_compl,frontier_compl]
  have hRF : frontier R ⊆ Uᶜ := by
    intro x hx hu
    exact hx.2 (hcl (subset_closure hu))
  have hFR : frontier U ⊆ R := (frontier_subset_closure.trans hcl).trans interior_subset
  rw [inter_eq_left.mpr hRF,inter_eq_right.mpr hFR]

theorem finite_spherical_hole_retained_region
    {ι : Type*} (s : Finset ι) (U : ι → Set X)
    {R : Set X} (hR : IsCompact R) (hRc : IsConnected R)
    (hU : ∀ i ∈ s, IsOpen (U i))
    (hcl : ∀ i ∈ s, closure (U i) ⊆ interior R)
    (hf : ∀ i ∈ s, IsConnected (frontier (U i)))
    (hdis : (s : Set ι).Pairwise fun i j => Disjoint (closure (U i)) (closure (U j))) :
    IsCompact (R \ ⋃ i ∈ s, U i) ∧ IsConnected (R \ ⋃ i ∈ s, U i) ∧
      frontier (R \ ⋃ i ∈ s, U i) = frontier R ∪ ⋃ i ∈ s, frontier (U i) ∧
      frontier R ⊆ R \ ⋃ i ∈ s, U i := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using And.intro hR (And.intro hRc hR.isClosed.frontier_subset)
  | @insert i s hi ih =>
    have hUs j hj := hU j (Finset.mem_insert_of_mem hj)
    have hcls j hj := hcl j (Finset.mem_insert_of_mem hj)
    have hfs j hj := hf j (Finset.mem_insert_of_mem hj)
    have hdiss : (s : Set ι).Pairwise fun j k => Disjoint (closure (U j)) (closure (U k)) :=
      hdis.mono (Finset.subset_insert i s)
    obtain ⟨hK,hKc,hKf,hKR⟩ := ih hUs hcls hfs hdiss
    have hi' : i ∈ insert i s := Finset.mem_insert_self i s
    have haway : Disjoint (closure (U i)) (⋃ j ∈ s, closure (U j)) := by
      apply disjoint_iUnion_right.mpr
      intro j
      apply disjoint_iUnion_right.mpr
      intro hj
      exact hdis hi' (Finset.mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj))
    have hinside : closure (U i) ⊆ interior (R \ ⋃ j ∈ s, U j) := by
      rw [sdiff_eq_compl_inter,interior_inter,interior_compl]
      intro x hx
      refine ⟨?_,hcl i hi' hx⟩
      rw [s.closure_biUnion]
      exact fun hh => disjoint_left.mp haway hx hh
    have hnewc := isConnected_sdiff_of_connected_frontier hK hKc (hU i hi')
      (hinside.trans interior_subset) (hf i hi')
    have hnewf := frontier_sdiff_open_of_closure_subset_interior hK.isClosed (hU i hi') hinside
    have heq : R \ ⋃ j ∈ insert i s, U j = (R \ ⋃ j ∈ s, U j) \ U i := by
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
      ext x
      simp only [mem_sdiff,mem_union,not_or]
      tauto
    rw [heq]
    refine ⟨hK.diff (hU i hi'),hnewc,?_,?_⟩
    · rw [hnewf,hKf]
      simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
      ac_rfl
    · intro x hx
      exact ⟨hKR hx,fun hu => hx.2 (hcl i hi' (subset_closure hu))⟩

end PoincareConjecture.M76

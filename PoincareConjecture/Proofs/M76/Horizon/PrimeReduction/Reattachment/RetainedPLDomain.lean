import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.ConnectedRetainedRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.LatticeSphereDomain
import PoincareConjecture.Proofs.M76.Wall.SphericalFrontierFilling









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X α : Type*} [TopologicalSpace X] [T2Space X]
  {e : α → OpenPartialHomeomorph X V3} {R : Set X}

omit [T2Space X] in
theorem PLDomain.finite_disjoint_hole_exterior
    {ι : Type*} (he : PLDomain e R) (s : Finset ι) (Q : ι → Set X)
    (hQ : ∀ i ∈ s, PLDomain e (Q i))
    (hinside : ∀ i ∈ s, Q i ⊆ interior R)
    (hdis : (s : Set ι).Pairwise fun i j => Disjoint (Q i) (Q j)) :
    PLDomain e (R \ ⋃ i ∈ s, interior (Q i)) ∧
      frontier (R \ ⋃ i ∈ s, interior (Q i)) =
        frontier R ∪ ⋃ i ∈ s, frontier (Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using he
  | @insert i s hi ih =>
    have hQs j hj := hQ j (Finset.mem_insert_of_mem hj)
    have hinsideS j hj := hinside j (Finset.mem_insert_of_mem hj)
    have hdisS : (s : Set ι).Pairwise fun j k => Disjoint (Q j) (Q k) :=
      hdis.mono (Finset.subset_insert i s)
    obtain ⟨hK,hKf⟩ := ih hQs hinsideS hdisS
    have hi' : i ∈ insert i s := Finset.mem_insert_self i s
    have hfront : Disjoint (frontier (R \ ⋃ j ∈ s, interior (Q j))) (frontier (Q i)) := by
      rw [hKf]
      apply disjoint_left.mpr
      intro x hx hxQ
      rcases hx with hxR | hx
      · exact hxR.2 (hinside i hi' ((hQ i hi').closed.frontier_subset hxQ))
      · obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hx
        exact disjoint_left.mp
          (hdis (Finset.mem_insert_of_mem hj) hi' (fun hji => hi (hji ▸ hj)))
          ((hQs j hj).closed.frontier_subset hxj) ((hQ i hi').closed.frontier_subset hxQ)
    have hdom := hK.inter_of_disjoint_frontiers (hQ i hi').closed_exterior
      (by rwa [(hQ i hi').frontier_closed_exterior])
    have hQinside : Q i ⊆ interior (R \ ⋃ j ∈ s, interior (Q j)) := by
      rw [sdiff_eq_compl_inter,interior_inter,interior_compl,s.closure_biUnion]
      intro x hx
      refine ⟨?_,hinside i hi' hx⟩
      intro hh
      obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hh
      rw [(hQs j hj).closure_interior] at hxj
      exact disjoint_left.mp
        (hdis hi' (Finset.mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj))) hx hxj
    have hf := frontier_sdiff_open_of_closure_subset_interior hK.closed isOpen_interior
      ((hQ i hi').closure_interior ▸ hQinside)
    have hfi : frontier (interior (Q i)) = frontier (Q i) := by
      simpa only [frontier_compl] using (hQ i hi').frontier_closed_exterior
    have heq : R \ ⋃ j ∈ insert i s, interior (Q j) =
        (R \ ⋃ j ∈ s, interior (Q j)) \ interior (Q i) := by
      simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left]
      ext x
      simp only [mem_sdiff,mem_union,not_or]
      tauto
    rw [heq]
    refine ⟨hdom,?_⟩
    rw [hf,hKf,hfi]
    simp only [Finset.mem_insert,iUnion_iUnion_eq_or_left]
    ac_rfl

theorem finite_ball_retained_PL_domain
    {ι : Type*} (he : PLDomain e R) (hR : IsCompact R) (hRc : IsConnected R)
    (s : Finset ι) (Q S : ι → Set X)
    (hQ : ∀ i ∈ s, IsCompact (Q i))
    (hS : ∀ i ∈ s, ChartwisePLSphere e (S i))
    (hfront : ∀ i ∈ s, frontier (Q i) = S i)
    (hball : ∀ i ∈ s, IsUnitBallPair V3 (Q i) (S i))
    (hinside : ∀ i ∈ s, Q i ⊆ interior R)
    (hdis : (s : Set ι).Pairwise fun i j => Disjoint (Q i) (Q j)) :
    IsCompact (R \ ⋃ i ∈ s, interior (Q i)) ∧
      IsConnected (R \ ⋃ i ∈ s, interior (Q i)) ∧
      PLDomain e (R \ ⋃ i ∈ s, interior (Q i)) ∧
      frontier (R \ ⋃ i ∈ s, interior (Q i)) = frontier R ∪ ⋃ i ∈ s, S i ∧
      frontier R ⊆ R \ ⋃ i ∈ s, interior (Q i) := by
  have hdomains i hi := (hS i hi).plDomain_of_unitBallPair (hQ i hi)
    (hfront i hi) (hball i hi) he.compatible he.cover
  obtain ⟨hdom,hf⟩ := he.finite_disjoint_hole_exterior s Q hdomains hinside hdis
  have hfi (i : ι) (hi : i ∈ s) : frontier (interior (Q i)) = S i := by
    simpa only [frontier_compl,hfront i hi] using (hdomains i hi).frontier_closed_exterior
  obtain ⟨hc,hconn,_,hold⟩ := finite_spherical_hole_retained_region s (fun i => interior (Q i))
    hR hRc (fun _ _ => isOpen_interior)
    (fun i hi => by rw [(hdomains i hi).closure_interior]; exact hinside i hi)
    (fun i hi => by rw [hfi i hi]; exact (hS i hi).compact_connected.2)
    (fun i hi j hj hij => by
      change Disjoint (closure (interior (Q i))) (closure (interior (Q j)))
      rw [(hdomains i hi).closure_interior,(hdomains j hj).closure_interior]
      exact hdis hi hj hij)
  refine ⟨hc,hconn,hdom,?_,hold⟩
  rw [hf]
  congr 1
  apply iUnion_congr
  intro i
  apply iUnion_congr
  intro hi
  exact hfront i hi

end PoincareConjecture.M76

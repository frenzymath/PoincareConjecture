import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.LatticeCollarCoverObstruction

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.MarkedSphereCut
local notation "V3" => (Fin 3 → ℝ)

variable {ι κ α ν : Type*} [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
  {R : Set (LatticeHandleAmbient ι κ L)} (c : MarkedSphereCut e R ν)

theorem outermost_retained_region_ne_collar_closure_of_univ
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hR : R = univ)
    (Q : ν × Bool → Set (LatticeHandleAmbient ι κ L)) (t : Finset (ν × Bool))
    (hfrontQ : ∀ b,frontier (Q b) = c.ports b)
    (hball : ∀ b,IsUnitBallPair V3 (Q b) (c.ports b))
    (hdis : Pairwise fun b d : t => Disjoint (Q b) (Q d))
    (homitted : ∀ b,b ∉ t → ∃ d : t,Q b ⊆ interior (Q d))
    (hfrontA : frontier (R \ ⋃ d : t,interior (Q d)) =
      frontier R ∪ ⋃ d : t,c.ports d) (i : ν) :
    R \ ⋃ d : t,interior (Q d) ≠ closure (c.collar i) := by
  classical
  intro heq
  have hselected (b : Bool) : (i,b) ∈ t := by
    by_contra hn
    obtain ⟨d,hd⟩ := homitted (i,b) hn
    obtain ⟨x,hx⟩ := (c.portPL (i,b)).isConnected.nonempty
    have hxA : x ∈ R \ ⋃ d : t,interior (Q d) :=
      heq.symm ▸ c.portClosure (i,b) hx
    exact hxA.2 (mem_iUnion.mpr ⟨d,hd ((hball (i,b)).1 hx)⟩)
  have hwhich (d : t) : (d : ν × Bool) = (i,false) ∨ (d : ν × Bool) = (i,true) := by
    obtain ⟨x,hx⟩ := (c.portPL d).isConnected.nonempty
    have hxfront : x ∈ frontier (closure (c.collar i)) := by
      rw [← heq,hfrontA]
      exact Or.inr (mem_iUnion.mpr ⟨d,hx⟩)
    have hxends := frontier_closure_subset hxfront
    rw [c.frontier_collar] at hxends
    rcases hxends with hx0 | hx1
    · left
      by_contra hn
      exact disjoint_left.mp (c.portDisjoint hn) hx hx0
    · right
      by_contra hn
      exact disjoint_left.mp (c.portDisjoint hn) hx hx1
  have hpairDis : Disjoint (Q (i,false)) (Q (i,true)) :=
    hdis (i := ⟨(i,false),hselected false⟩) (j := ⟨(i,true),hselected true⟩)
      (by intro h; have hh := congrArg (fun d : t => d.val.2) h; cases hh)
  have hoverlap (b : Bool) : closure (c.collar i) ∩ Q (i,b) = c.ports (i,b) := by
    ext x
    constructor
    · rintro ⟨hxC,hxQ⟩
      have hxA : x ∈ R \ ⋃ d : t,interior (Q d) := heq.symm ▸ hxC
      rw [← hfrontQ]
      exact ⟨subset_closure hxQ,fun hi =>
        hxA.2 (mem_iUnion.mpr ⟨⟨(i,b),hselected b⟩,hi⟩)⟩
    · intro hx
      exact ⟨c.portClosure (i,b) hx,(hball (i,b)).1 hx⟩
  apply c.not_collar_two_balls_cover_ambient L i hdim
    (fun b => Q (i,b)) (fun b => hball (i,b)) hpairDis hoverlap
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ R \ ⋃ d : t,interior (Q d)
  · exact Or.inl (Or.inl (heq ▸ hx))
  · have hxR : x ∈ R := hR.symm ▸ mem_univ x
    have hxunion : x ∈ ⋃ d : t,interior (Q d) := by
      by_contra hn
      exact hx ⟨hxR,hn⟩
    obtain ⟨d,hd⟩ := mem_iUnion.mp hxunion
    rcases hwhich d with hd0 | hd1
    · exact Or.inl (Or.inr (hd0 ▸ interior_subset hd))
    · exact Or.inr (hd1 ▸ interior_subset hd)

theorem outermost_retained_region_eq_component_of_univ
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hR : R = univ)
    (Q : ν × Bool → Set (LatticeHandleAmbient ι κ L)) (t : Finset (ν × Bool))
    (hfrontQ : ∀ b,frontier (Q b) = c.ports b)
    (hball : ∀ b,IsUnitBallPair V3 (Q b) (c.ports b))
    (hdis : Pairwise fun b d : t => Disjoint (Q b) (Q d))
    (homitted : ∀ b,b ∉ t → ∃ d : t,Q b ⊆ interior (Q d))
    (hfrontA : frontier (R \ ⋃ d : t,interior (Q d)) =
      frontier R ∪ ⋃ d : t,c.ports d)
    (hA : PLDomain e (R \ ⋃ d : t,interior (Q d)))
    (hAc : IsConnected (R \ ⋃ d : t,interior (Q d))) :
    (R \ ⋃ d : t,interior (Q d)) ⊆ c.carrier ∧
      ∀ x ∈ R \ ⋃ d : t,interior (Q d),
        connectedComponentIn c.carrier x = R \ ⋃ d : t,interior (Q d) := by
  have hfront : frontier (R \ ⋃ d : t,interior (Q d)) ⊆
      frontier R ∪ ⋃ b,c.ports b := by
    rw [hfrontA]
    exact union_subset_union_right _ (iUnion_subset fun d => subset_iUnion _ (d : ν × Bool))
  have hAC : (R \ ⋃ d : t,interior (Q d)) ⊆ c.carrier := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxunion
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxunion
    rcases c.retained_region_collar_alternative hA hAc hfront
      (c.outermost_port_dichotomy Q t hfrontQ homitted hfrontA) i with hd | heq
    · exact disjoint_left.mp hd hx hi
    · exact c.outermost_retained_region_ne_collar_closure_of_univ L hdim hR
        Q t hfrontQ hball hdis homitted hfrontA i heq
  exact ⟨hAC,fun _ hx => c.retained_region_eq_component hA hAc hAC hfront hx⟩

end PoincareConjecture.M76.MarkedSphereCut

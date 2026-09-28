import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.MarkedSphereCut
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.PLDomainInteriorConnected
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.RelativeFrontierOpenness
import PoincareConjecture.Proofs.M76.Rigidity.OriginalSphereConnected








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

namespace MarkedSphereCut

variable {X α κ : Type*} [TopologicalSpace X]
  {e : α → OpenPartialHomeomorph X V3} {R : Set X}
  (c : MarkedSphereCut e R κ)

theorem port_subset_carrier (b : κ × Bool) : c.ports b ⊆ c.carrier := by
  intro x hx
  apply c.plCut.closed.frontier_subset
  rw [c.frontierCut]
  exact Or.inr (mem_iUnion.mpr ⟨b,hx⟩)

theorem isConnected_collar (i : κ) : IsConnected (c.collar i) := by
  have : ConnectedSpace (c.spheres i) :=
    isConnected_iff_connectedSpace.mp (c.spherePL i).isConnected
  have hsource : IsConnected ((univ : Set (c.spheres i)) ×ˢ
      Ioo (0 : unitInterval) 1) := isConnected_univ.prod (isConnected_Ioo zero_lt_one)
  have himage : (fun z => (c.product i z : X)) ''
      ((univ : Set (c.spheres i)) ×ˢ Ioo (0 : unitInterval) 1) = c.collar i := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (c.openCoordinates i z).mpr hz.2
    · intro hx
      obtain ⟨z,hz⟩ := (c.product i).surjective ⟨x,subset_closure hx⟩
      have hv : (c.product i z : X) = x := congrArg Subtype.val hz
      refine ⟨z,⟨mem_univ _,?_⟩,hv⟩
      exact (c.openCoordinates i z).mp (hv.symm ▸ hx)
  rw [← himage]
  exact hsource.image _ (continuous_subtype_val.comp (c.product i).continuous).continuousOn

theorem frontier_collar (i : κ) :
    frontier (c.collar i) = c.ports (i,false) ∪ c.ports (i,true) := by
  rw [← c.collarContact i]
  ext x
  constructor
  · intro hx
    refine ⟨hx.1,⟨interior_subset (c.collarInterior i hx.1),?_⟩⟩
    intro hall
    obtain ⟨j,hj⟩ := mem_iUnion.mp hall
    by_cases hij : i = j
    · subst j
      exact hx.2 ((c.collarOpen i).interior_eq.symm ▸ hj)
    · exact disjoint_left.mp (c.collarDisjoint hij) hx.1 (subset_closure hj)
  · rintro ⟨hx,hR,hnot⟩
    exact ⟨hx,fun hi => hnot (mem_iUnion.mpr ⟨i,interior_subset hi⟩)⟩

theorem disjoint_collar_frontier_cut (i : κ) :
    Disjoint (frontier R ∪ ⋃ b,c.ports b) (c.collar i) := by
  apply disjoint_left.mpr
  intro x hx hxi
  rcases hx with hx | hx
  · exact hx.2 (c.collarInterior i (subset_closure hxi))
  · obtain ⟨b,hb⟩ := mem_iUnion.mp hx
    exact (c.port_subset_carrier b hb).2 (mem_iUnion.mpr ⟨i,hxi⟩)

theorem retained_region_collar_alternative {A : Set X}
    (hA : PLDomain e A) (hAc : IsConnected A)
    (hfront : frontier A ⊆ frontier R ∪ ⋃ b,c.ports b)
    (hports : ∀ b,c.ports b ⊆ frontier A ∨ Disjoint (c.ports b) A)
    (i : κ) : Disjoint A (c.collar i) ∨ A = closure (c.collar i) := by
  by_cases hdis : Disjoint A (c.collar i)
  · exact Or.inl hdis
  right
  obtain ⟨x,hxA,hxO⟩ := not_disjoint_iff.mp hdis
  have havoid : Disjoint (frontier A) (c.collar i) :=
    (c.disjoint_collar_frontier_cut i).mono_left hfront
  have hxint : x ∈ interior A := by
    by_contra hn
    exact disjoint_left.mp havoid ⟨subset_closure hxA,hn⟩ hxO
  have hOA : c.collar i ⊆ interior A :=
    (c.isConnected_collar i).isPreconnected.m76_subset_of_disjoint_frontier
      isOpen_interior (havoid.mono_left frontier_interior_subset) ⟨x,hxO,hxint⟩
  have hclA : closure (c.collar i) ⊆ A := by
    simpa only [hA.closure_interior] using closure_mono hOA
  have hport (b : Bool) : c.ports (i,b) ⊆ frontier A := by
    rcases hports (i,b) with h | h
    · exact h
    · obtain ⟨y,hy⟩ := (c.portPL (i,b)).isConnected.nonempty
      exact (disjoint_left.mp h hy (hclA (c.portClosure (i,b) hy))).elim
  have hfrontO : frontier (c.collar i) ⊆ frontier A := by
    rw [c.frontier_collar]
    exact union_subset (hport false) (hport true)
  have hAO : interior A ⊆ c.collar i :=
    (hA.isConnected_interior hAc).isPreconnected.m76_subset_of_disjoint_frontier
      (c.collarOpen i)
      (disjoint_left.mpr fun y hy hya => (hfrontO hy).2 hya) ⟨x,hxint,hxO⟩
  exact subset_antisymm (hA.closure_interior ▸ closure_mono hAO) hclA

theorem retained_region_subset_carrier_of_nonempty_old_boundary {A : Set X}
    (hA : PLDomain e A) (hAc : IsConnected A) (hAR : A ⊆ R)
    (hfront : frontier A ⊆ frontier R ∪ ⋃ b,c.ports b)
    (hports : ∀ b,c.ports b ⊆ frontier A ∨ Disjoint (c.ports b) A)
    (hboundary : frontier R ⊆ A) (hne : (frontier R).Nonempty) :
    A ⊆ c.carrier := by
  intro x hx
  refine ⟨hAR hx,?_⟩
  intro hall
  obtain ⟨i,hi⟩ := mem_iUnion.mp hall
  rcases c.retained_region_collar_alternative hA hAc hfront hports i with hd | heq
  · exact disjoint_left.mp hd hx hi
  · obtain ⟨y,hy⟩ := hne
    exact hy.2 (c.collarInterior i (heq ▸ hboundary hy))

theorem retained_region_eq_component {A : Set X}
    (hA : PLDomain e A) (hAc : IsConnected A) (hAC : A ⊆ c.carrier)
    (hfront : frontier A ⊆ frontier R ∪ ⋃ b,c.ports b)
    {x : X} (hx : x ∈ A) : connectedComponentIn c.carrier x = A := by
  have hfront' : frontier A ⊆ frontier c.carrier := by
    simpa only [carrier,c.frontierCut] using hfront
  have hopen : IsOpen ((Subtype.val : c.carrier → X) ⁻¹' A) := by
    change IsOpen ((Subtype.val : {x : X // x ∈ R \ ⋃ i,c.collar i} → X) ⁻¹' A)
    simpa only [sdiff_empty] using
      c.plCut.isOpen_relative_sdiff_of_frontier_subset hA.closure_interior
        hAC isClosed_empty (hfront'.trans subset_union_left)
  have hclopen : IsClopen ((Subtype.val : c.carrier → X) ⁻¹' A) :=
    ⟨hA.closed.preimage continuous_subtype_val,hopen⟩
  apply subset_antisymm
  · rw [connectedComponentIn_eq_image (hAC hx)]
    rintro y ⟨z,hz,rfl⟩
    exact hclopen.connectedComponent_subset hx hz
  · exact hAc.isPreconnected.subset_connectedComponentIn hx hAC

theorem outermost_port_dichotomy
    (Q : κ × Bool → Set X) (t : Finset (κ × Bool))
    (hfrontQ : ∀ b,frontier (Q b) = c.ports b)
    (homitted : ∀ b,b ∉ t → ∃ d : t,Q b ⊆ interior (Q d))
    (hfrontA : frontier (R \ ⋃ d : t,interior (Q d)) =
      frontier R ∪ ⋃ d : t,c.ports d) :
    ∀ b,c.ports b ⊆ frontier (R \ ⋃ d : t,interior (Q d)) ∨
      Disjoint (c.ports b) (R \ ⋃ d : t,interior (Q d)) := by
  intro b
  by_cases hb : b ∈ t
  · left
    rw [hfrontA]
    exact fun x hx => Or.inr (mem_iUnion.mpr ⟨⟨b,hb⟩,hx⟩)
  · right
    obtain ⟨d,hd⟩ := homitted b hb
    apply disjoint_left.mpr
    intro x hx hxA
    have hxcl : x ∈ closure (Q b) := frontier_subset_closure (hfrontQ b ▸ hx)
    have hnot : x ∉ interior (Q d) := fun h => hxA.2 (mem_iUnion.mpr ⟨d,h⟩)
    have hclosure : closure (Q b) ⊆ closure (interior (Q d)) := closure_mono hd
    have hxfront : x ∈ frontier (Q d) :=
      ⟨(closure_mono interior_subset) (hclosure hxcl),hnot⟩
    have hbd : b ≠ (d : κ × Bool) := fun heq => hb (heq ▸ d.property)
    exact disjoint_left.mp (c.portDisjoint hbd) hx (hfrontQ d ▸ hxfront)

theorem outermost_retained_region_eq_component
    (Q : κ × Bool → Set X) (t : Finset (κ × Bool))
    (hfrontQ : ∀ b,frontier (Q b) = c.ports b)
    (homitted : ∀ b,b ∉ t → ∃ d : t,Q b ⊆ interior (Q d))
    (hfrontA : frontier (R \ ⋃ d : t,interior (Q d)) =
      frontier R ∪ ⋃ d : t,c.ports d)
    (hA : PLDomain e (R \ ⋃ d : t,interior (Q d)))
    (hAc : IsConnected (R \ ⋃ d : t,interior (Q d)))
    (hboundary : frontier R ⊆ R \ ⋃ d : t,interior (Q d))
    (hne : (frontier R).Nonempty) :
    (R \ ⋃ d : t,interior (Q d)) ⊆ c.carrier ∧
      ∀ x ∈ R \ ⋃ d : t,interior (Q d),
        connectedComponentIn c.carrier x = R \ ⋃ d : t,interior (Q d) := by
  have hfront : frontier (R \ ⋃ d : t,interior (Q d)) ⊆
      frontier R ∪ ⋃ b,c.ports b := by
    rw [hfrontA]
    exact union_subset_union_right _ (iUnion_subset fun d => subset_iUnion _ (d : κ × Bool))
  have hAC := c.retained_region_subset_carrier_of_nonempty_old_boundary
    hA hAc sdiff_subset hfront (c.outermost_port_dichotomy Q t hfrontQ homitted hfrontA)
    hboundary hne
  exact ⟨hAC,fun _ hx => c.retained_region_eq_component hA hAc hAC hfront hx⟩

end MarkedSphereCut
end PoincareConjecture.M76

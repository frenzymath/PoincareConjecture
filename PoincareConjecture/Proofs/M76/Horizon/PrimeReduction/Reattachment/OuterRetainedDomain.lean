import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RetainedPLDomain
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.RetainedPortCore

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.outer_retained_domain
    {X α κ : Type*} [TopologicalSpace X] [T2Space X]
    {e : α → OpenPartialHomeomorph X V3} {R P : Set X}
    (c : MarkedSphereCut e R κ) (hP : IsCompact P) (heP : PLDomain e P)
    (hRP : R ⊆ interior P)
    (heB : PLDomain e (P \ ⋃ i,c.collar i))
    (hBfront : frontier (P \ ⋃ i,c.collar i) = frontier P ∪ ⋃ i,c.ports i)
    (Q : κ × Bool → Set X) (t : Finset (κ × Bool))
    (hQ : ∀ i : t, IsCompact (Q i))
    (hfrontQ : ∀ i : t, frontier (Q i) = c.ports i)
    (hball : ∀ i : t, IsUnitBallPair V3 (Q i) (c.ports i))
    (hinside : ∀ i : t, Q i ⊆ interior R)
    (hdis : Pairwise fun i j : t => Disjoint (Q i) (Q j))
    (hinner : (R \ ⋃ i : t, interior (Q i)) ⊆ c.carrier) :
    let A := P \ ⋃ i : t, interior (Q i)
    let B := P \ ⋃ i,c.collar i
    IsCompact A ∧ PLDomain e A ∧
      frontier A = frontier P ∪ ⋃ i : t,c.ports i ∧ frontier P ⊆ A ∧
      A ⊆ B ∧ IsClopen ((Subtype.val : B → X) ⁻¹' A) ∧
      IsCompact (B \ A) ∧ A ∩ R = R \ ⋃ i : t, interior (Q i) := by
  classical
  let A := P \ ⋃ i : t, interior (Q i)
  let B := P \ ⋃ i,c.collar i
  have hQR (i : t) : Q i ⊆ interior P := (hinside i).trans (interior_subset.trans hRP)
  have heQ (i : t) := (c.portPL i).plDomain_of_unitBallPair (hQ i) (hfrontQ i)
    (hball i) heP.compatible heP.cover
  obtain ⟨heA,hAf⟩ := heP.finite_disjoint_hole_exterior (Finset.univ : Finset t)
    (fun i => Q i) (fun i _ => heQ i) (fun i _ => hQR i) (fun _ _ _ _ hij => hdis hij)
  simp only [Finset.mem_univ,iUnion_true] at heA hAf
  have hAf' : frontier A = frontier P ∪ ⋃ i : t,c.ports i := by simpa only [hfrontQ] using hAf
  have hAc : IsCompact A := hP.of_isClosed_subset heA.closed sdiff_subset
  have hBA : A ⊆ B := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxO
    obtain ⟨i,hi⟩ := mem_iUnion.mp hxO
    have hxR : x ∈ R := interior_subset (c.collarInterior i (subset_closure hi))
    exact (hinner ⟨hxR,hx.2⟩).2 (mem_iUnion.mpr ⟨i,hi⟩)
  have hfront : frontier A ⊆ frontier B := by
    rw [hAf',hBfront]
    exact union_subset_union_right _ (iUnion_subset fun i => subset_iUnion _ (i : κ × Bool))
  have hopen : IsOpen ((Subtype.val : B → X) ⁻¹' A) := by
    simpa only [sdiff_empty] using heB.isOpen_relative_sdiff_of_frontier_subset
      heA.closure_interior hBA isClosed_empty (hfront.trans subset_union_left)
  have hBc : IsCompact B := hP.of_isClosed_subset heB.closed sdiff_subset
  let : CompactSpace B := isCompact_iff_compactSpace.mp hBc
  have hrest : IsCompact (B \ A) := by
    have h := hopen.isClosed_compl.isCompact.image continuous_subtype_val
    have heq : (Subtype.val : B → X) '' ((Subtype.val : B → X) ⁻¹' A)ᶜ = B \ A := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact ⟨y.property,hy⟩
      · rintro ⟨hxB,hxA⟩
        exact ⟨⟨x,hxB⟩,hxA,rfl⟩
    rwa [heq] at h
  refine ⟨hAc,heA,hAf',?_,hBA,⟨heA.closed.preimage continuous_subtype_val,hopen⟩,hrest,?_⟩
  · intro x hx
    refine ⟨heP.closed.frontier_subset hx,?_⟩
    intro hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact hx.2 (hQR i (interior_subset hi))
  · ext x
    constructor
    · rintro ⟨hxA,hxR⟩
      exact ⟨hxR,hxA.2⟩
    · rintro ⟨hxR,hxQ⟩
      exact ⟨⟨interior_subset (hRP hxR),hxQ⟩,hxR⟩

end PoincareConjecture.M76

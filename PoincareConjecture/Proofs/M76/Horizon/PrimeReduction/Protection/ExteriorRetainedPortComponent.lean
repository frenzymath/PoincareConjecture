import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.OriginalRetainedPortComponent
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.OriginalExteriorNonspherical

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem HamiltonMarkedProtectedBall.exists_exterior_retained_port_component
    {ι κ α ν : Type*} [Fintype ι] [Fintype κ] [Finite ν]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)} (bD : HamiltonMarkedProtectedBall ι κ L e D)
    (c : MarkedSphereCut e (closure (latticeHandleDomain ι κ L \ D)) ν)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3) (hi : Fintype.card ι = 1) :
    let R := closure (latticeHandleDomain ι κ L \ D)
    ∃ (Q : ν × Bool → Set (LatticeHandleAmbient ι κ L)) (t : Finset (ν × Bool)),
      (∀ i, IsCompact (Q i) ∧ frontier (Q i) = c.ports i ∧
        IsUnitBallPair V3 (Q i) (c.ports i) ∧ Q i ⊆ interior R) ∧
      Pairwise (fun i j : t => Disjoint (Q i) (Q j)) ∧
      let A := R \ ⋃ i : t, interior (Q i)
      IsCompact A ∧ IsConnected A ∧ PLDomain e A ∧
      frontier A = frontier R ∪ ⋃ i : t, c.ports i ∧ frontier R ⊆ A ∧
      A ⊆ c.carrier ∧ (∀ x ∈ A, connectedComponentIn c.carrier x = A) ∧
      (∀ i : t, A ∩ Q i = c.ports i) ∧
      (∀ i, (c.ports i ∩ A).Nonempty ↔ i ∈ t) ∧
      A ∪ ⋃ i : t, Q i = R := by
  classical
  let R := closure (latticeHandleDomain ι κ L \ D)
  obtain ⟨hR,hsub,_,_,hint,_,_⟩ := bD.closed_complement_geometry he hdim hi
  have heR := bD.plDomain_closed_complement he hdim hi
  have hRc := bD.isConnected_closed_complement he hdim hi
  obtain ⟨Q,hQ,hfront,hball,_,hinside,_,t,htdis,_,_,_,homitted⟩ :=
    exists_outermost_lattice_sphere_balls L c.ports c.portPL he hdim
      (fun i => ((c.portClosure i).trans (c.collarInterior i.1)).trans (interior_mono hsub)) c.portDisjoint
  have hprotected := bD.subset_residual_exterior (by omega) Q
    (fun i => (hQ i).isClosed) hinside (fun i => by
      rw [hfront i]
      apply disjoint_left.mpr
      intro x hxD hxS
      have hxE := c.collarInterior i.1 (c.portClosure i hxS)
      rw [hint] at hxE
      exact hxE.2 hxD)
  have hinsideE (i : ν × Bool) : Q i ⊆ interior R := by
    intro x hx
    change x ∈ interior (closure (latticeHandleDomain ι κ L \ D))
    rw [hint]
    exact ⟨hinside i hx, fun hxD =>
      hprotected.2 (Or.inl hxD) (mem_iUnion.mpr ⟨i,hx⟩)⟩
  let A := R \ ⋃ i : t, interior (Q i)
  obtain ⟨hA,hAc,heA,hAf,hRA⟩ := finite_ball_retained_PL_domain heR hR hRc
    (Finset.univ : Finset t) (fun i => Q i) (fun i => c.ports i)
    (fun i _ => hQ i) (fun i _ => c.portPL i) (fun i _ => hfront i)
    (fun i _ => hball i) (fun i _ => hinsideE i) (fun _ _ _ _ hij => htdis hij)
  simp only [Finset.mem_univ,iUnion_true] at hA hAc heA hAf hRA
  have hcore : A ⊆ c.carrier ∧ ∀ x ∈ A, connectedComponentIn c.carrier x = A :=
    c.outermost_retained_region_eq_component Q t hfront homitted hAf heA hAc hRA
      (bD.isConnected_closed_complement_frontier he hdim hi).nonempty
  obtain ⟨hAC,hcomponent⟩ := hcore
  have hcontact (i : t) : A ∩ Q i = c.ports i := by
    rw [←hfront i,(hQ i).isClosed.frontier_eq]
    apply Subset.antisymm
    · rintro x ⟨hxA,hxQ⟩
      exact ⟨hxQ,fun hx => hxA.2 (mem_iUnion.mpr ⟨i,hx⟩)⟩
    · rintro x ⟨hxQ,hxint⟩
      refine ⟨⟨interior_subset (hinsideE i hxQ),?_⟩,hxQ⟩
      intro hx
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact hxint (hij.symm ▸ hxj)
      · exact disjoint_left.mp (htdis hij) hxQ (interior_subset hxj)
  refine ⟨Q,t,fun i => ⟨hQ i,hfront i,hball i,hinsideE i⟩,htdis,
    hA,hAc,heA,hAf,hRA,hAC,hcomponent,hcontact,?_,?_⟩
  · intro i
    constructor
    · rintro ⟨x,hxi,hxA⟩
      by_contra hi
      obtain ⟨j,hj⟩ := homitted i hi
      exact hxA.2 (mem_iUnion.mpr ⟨j,hj ((hball i).1 hxi)⟩)
    · intro hi
      obtain ⟨x,hx⟩ := (c.portPL i).isConnected.nonempty
      exact ⟨x,hx,((hcontact ⟨i,hi⟩).symm.subset hx).1⟩
  · apply Subset.antisymm
    · exact union_subset sdiff_subset (iUnion_subset fun i => (hinsideE i).trans interior_subset)
    · intro x hx
      by_cases hh : x ∈ ⋃ i : t, Q i
      · exact Or.inr hh
      · exact Or.inl ⟨hx,fun hint => hh (iUnion_mono (fun _ => interior_subset) hint)⟩

end PoincareConjecture.M76

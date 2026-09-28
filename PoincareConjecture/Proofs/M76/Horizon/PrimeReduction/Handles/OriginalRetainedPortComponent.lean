import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.LatticeSphereBallFamily
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.RetainedPortCore
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.ZeroRetainedPortCore
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.ProtectedResidualExterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RetainedPLDomain
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonMarkedApproximation

set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.exists_original_retained_port_component
    {ι κ α ν : Type*} [Fintype ι] [Fintype κ] [Finite ν]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    (c : MarkedSphereCut e (latticeHandleDomain ι κ L) ν)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    {D : Set (LatticeHandleAmbient ι κ L)} (bD : HamiltonMarkedProtectedBall ι κ L e D) :
    let R := latticeHandleDomain ι κ L
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
  let R := latticeHandleDomain ι κ L
  have hR : IsCompact R := isCompact_latticeHandleDomain ι κ L
  have hquot : IsConnected (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup)) := by
    have h := (isConnected_univ : IsConnected (univ : Set (κ → ℝ))).image
      (QuotientAddGroup.mk : (κ → ℝ) → ((κ → ℝ) ⧸ L.toAddSubgroup))
      QuotientAddGroup.continuous_mk.continuousOn
    simpa only [image_univ,range_eq_univ.mpr QuotientAddGroup.mk_surjective] using h
  have hRc : IsConnected R := ((convex_closedBall (0 : ι → ℝ) 1).isConnected
    ⟨0,mem_closedBall_self zero_le_one⟩).prod hquot
  obtain ⟨Q,hQ,hfront,hball,_,hinside,_,t,htdis,_,_,_,homitted⟩ :=
    exists_outermost_lattice_sphere_balls L c.ports c.portPL he hdim
      (fun i => (c.portClosure i).trans (c.collarInterior i.1)) c.portDisjoint
  let A := R \ ⋃ i : t, interior (Q i)
  obtain ⟨hA,hAc,heA,hAf,hRA⟩ := finite_ball_retained_PL_domain he hR hRc
    (Finset.univ : Finset t) (fun i => Q i) (fun i => c.ports i)
    (fun i _ => hQ i) (fun i _ => c.portPL i) (fun i _ => hfront i)
    (fun i _ => hball i) (fun i _ => hinside i) (fun _ _ _ _ hij => htdis hij)
  simp only [Finset.mem_univ,iUnion_true] at hA hAc heA hAf hRA
  have hcore : A ⊆ c.carrier ∧ ∀ x ∈ A, connectedComponentIn c.carrier x = A := by
    by_cases hpos : 0 < Fintype.card ι
    · obtain ⟨p,_,hp⟩ := bD.boundary_contact_nonempty hpos
      exact c.outermost_retained_region_eq_component Q t hfront homitted hAf heA hAc hRA ⟨p,hp⟩
    · have hi : Fintype.card ι = 0 := by omega
      let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hi
      have hRuniv : R = univ := by
        apply eq_univ_of_forall
        intro x
        refine ⟨?_,mem_univ _⟩
        rw [Subsingleton.elim x.1 0]
        exact mem_closedBall_self zero_le_one
      exact c.outermost_retained_region_eq_component_of_univ L hdim hRuniv
        Q t hfront hball htdis homitted hAf heA hAc
  obtain ⟨hAC,hcomponent⟩ := hcore
  have hcontact (i : t) : A ∩ Q i = c.ports i := by
    rw [←hfront i,(hQ i).isClosed.frontier_eq]
    apply Subset.antisymm
    · rintro x ⟨hxA,hxQ⟩
      exact ⟨hxQ,fun hx => hxA.2 (mem_iUnion.mpr ⟨i,hx⟩)⟩
    · rintro x ⟨hxQ,hxint⟩
      refine ⟨⟨interior_subset (hinside i hxQ),?_⟩,hxQ⟩
      intro hx
      obtain ⟨j,hxj⟩ := mem_iUnion.mp hx
      by_cases hij : i = j
      · exact hxint (hij.symm ▸ hxj)
      · exact disjoint_left.mp (htdis hij) hxQ (interior_subset hxj)
  refine ⟨Q,t,fun i => ⟨hQ i,hfront i,hball i,hinside i⟩,htdis,
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
    · exact union_subset sdiff_subset (iUnion_subset fun i => (hinside i).trans interior_subset)
    · intro x hx
      by_cases hh : x ∈ ⋃ i : t, Q i
      · exact Or.inr hh
      · exact Or.inl ⟨hx,fun hint => hh (iUnion_mono (fun _ => interior_subset) hint)⟩

end PoincareConjecture.M76

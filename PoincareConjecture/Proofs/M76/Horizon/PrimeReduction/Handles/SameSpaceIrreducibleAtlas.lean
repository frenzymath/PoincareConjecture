import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.OriginalRetainedPortComponent
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.OpenRetainedModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.OpenSubcarrierHomeomorph
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.PartialIrreducibilityTransport

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem MarkedSphereCut.exists_same_space_irreducible_atlas
    {ι κ α ν E β : Type*} [Fintype ι] [Fintype κ] [Finite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    (c : MarkedSphereCut e (latticeHandleDomain ι κ L) ν)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    {D₀ : Set (LatticeHandleAmbient ι κ L)} (bD : HamiltonMarkedProtectedBall ι κ L e D₀)
    {P : Set (LatticeHandleAmbient ι κ L)} (hP : IsCompact P) (heP : PLDomain e P)
    (hRP : latticeHandleDomain ι κ L ⊆ interior P)
    (heB : PLDomain e (P \ ⋃ i,c.collar i))
    (hBfront : frontier (P \ ⋃ i,c.collar i) = frontier P ∪ ⋃ i,c.ports i)
    (f : LatticeHandleAmbient ι κ L → E) (hf : Continuous f)
    (hfPL : ∀ i, LocallyPiecewiseAffineOn (f ∘ (e i).symm) (e i).target)
    (hfi : InjOn f (P \ ⋃ i,c.collar i))
    (C : ν × Bool → Set E) (hC : ∀ i, IsFinitePLBallPair V3 (C i) (f '' c.ports i))
    (hdis : Pairwise fun i j => Disjoint (C i) (C j))
    (hcontact : ∀ i, (f '' (P \ ⋃ j,c.collar j)) ∩ C i = f '' c.ports i)
    {W : Set E} (hW : W = (f '' (P \ ⋃ i,c.collar i) ∪ ⋃ i,C i) \ f '' frontier P)
    (hDW : (f '' c.carrier ∪ ⋃ i,C i) ⊆ W)
    (atlas : β → OpenPartialHomeomorph W V3) (ha : PLDomain atlas univ)
    (hrep : ∀ j, ∃ (A : Set E) (a : E → V3), FinitePiecewiseAffineOn a A ∧
      ∀ x ∈ (atlas j).source, (x : E) ∈ A ∧ atlas j x = a x)
    (hI : IsPLIrreducible atlas ((Subtype.val : W → E) ⁻¹' (f '' c.carrier ∪ ⋃ i,C i)))
    (hDc : IsCompact ((Subtype.val : W → E) ⁻¹' (f '' c.carrier ∪ ⋃ i,C i))) :
    let R := latticeHandleDomain ι κ L
    ∃ (Q : ν × Bool → Set (LatticeHandleAmbient ι κ L)) (t : Finset (ν × Bool)),
      (∀ i, IsCompact (Q i) ∧ frontier (Q i) = c.ports i ∧
        IsUnitBallPair V3 (Q i) (c.ports i) ∧ Q i ⊆ interior R) ∧
      Pairwise (fun i j : t => Disjoint (Q i) (Q j)) ∧
      let O := (⋃ i : t,Q i)ᶜ
      IsOpen O ∧ frontier R ⊆ O ∧ (O ∩ interior R).Nonempty ∧
      ∃ a : (α ⊕ β) → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3,
        IsPLIrreducible a R ∧
        ChartwisePLOn e a (ContinuousMap.id R) ((Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' O) ∧
        ChartwisePLOn a e (ContinuousMap.id R) ((Subtype.val : R → LatticeHandleAmbient ι κ L) ⁻¹' O) := by
  classical
  subst W
  let R := latticeHandleDomain ι κ L
  let B := P \ ⋃ i,c.collar i
  let W := (f '' B ∪ ⋃ i,C i) \ f '' frontier P
  obtain ⟨Q,t,hQ,htdis,hAc,hAconn,heA,hAf,_,hAC,hcomponent,_,hselected,_⟩ :=
    c.exists_original_retained_port_component L he hdim bD
  let A := R \ ⋃ i : t,interior (Q i)
  let T := f '' A ∪ ⋃ i : t,C i
  let AP := P \ ⋃ i : t,interior (Q i)
  let V := (f '' AP ∪ ⋃ i : t,C i) \ f '' frontier P
  have hCB : c.carrier ⊆ B := fun _ hx => ⟨interior_subset (hRP hx.1),hx.2⟩
  have hcontactInner (i : ν × Bool) : (f '' c.carrier) ∩ C i = f '' c.ports i := by
    apply Subset.antisymm
    · exact (inter_subset_inter_left _ (image_mono hCB)).trans (hcontact i).subset
    · exact subset_inter (image_mono (c.port_subset_carrier i))
        ((hcontact i).symm.subset.trans inter_subset_right)
  obtain ⟨x,hx⟩ := hAconn.nonempty
  have hcc : connectedComponentIn (f '' c.carrier ∪ ⋃ i,C i) (f x) = T :=
    componentIn_selected_caps c.compactCut hAC hx (hcomponent x hx)
      c.ports c.port_subset_carrier t hselected f hf (hfi.mono hCB) C hC hdis hcontactInner
  have hxD : f x ∈ f '' c.carrier ∪ ⋃ i,C i := Or.inl (mem_image_of_mem f (hAC hx))
  have hIT := irreducible_ambient_component_preimage hDW atlas hI hDc hxD hcc
  have hTD : T ⊆ f '' c.carrier ∪ ⋃ i,C i :=
    hcc.symm.subset.trans (connectedComponentIn_subset _ _)
  obtain ⟨hVW,hVopen,H,hHF,hHR⟩ := c.exists_open_retained_model hP heP hRP heB hBfront
    Q t (fun i => (hQ i).1) (fun i => (hQ i).2.1) (fun i => (hQ i).2.2.1)
    (fun i => (hQ i).2.2.2) htdis hAC hselected f hf hfi C hC hdis hcontact
  let : Nonempty (interior P) := ⟨⟨x,hRP hx.1⟩⟩
  obtain ⟨M,hMs,_,hMval⟩ := exists_open_subcarrier_partial_homeomorph
    isOpen_interior hVW hVopen H
  have hTV : T ⊆ V := by
    intro y hy
    refine ⟨?_,(hDW (hTD hy)).2⟩
    have hAAP : A ⊆ AP := fun _ hz => ⟨interior_subset (hRP hz.1),hz.2⟩
    exact union_subset_union (image_mono hAAP) subset_rfl hy
  have hMT : M '' R = (Subtype.val : W → E) ⁻¹' T :=
    image_mark_of_open_subcarrier_partial_homeomorph H M hMval hRP hTV hHR
  let O := (⋃ i : t,Q i)ᶜ
  have hO : IsOpen O := (isClosed_iUnion_of_finite fun i : t => (hQ i).1.isClosed).isOpen_compl
  have hfront : frontier R ⊆ O := by
    intro y hy hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    exact hy.2 ((hQ i).2.2.2 hi)
  have hOne : (O ∩ interior R).Nonempty := by
    obtain ⟨y,hy⟩ := (heA.isConnected_interior hAconn).nonempty
    refine ⟨y,?_,interior_mono (show A ⊆ R from sdiff_subset) hy⟩
    intro hh
    obtain ⟨i,hi⟩ := mem_iUnion.mp hh
    have hyfront : y ∈ frontier (Q i) := ⟨subset_closure hi,fun hint =>
      (interior_subset hy).2 (mem_iUnion.mpr ⟨i,hint⟩)⟩
    have hyAf : y ∈ frontier A := hAf.symm.subset
      (Or.inr (mem_iUnion.mpr ⟨i,(hQ i).2.1.subset hyfront⟩))
    exact hyAf.2 hy
  have hcover : M.source ∪ O = univ := by
    rw [hMs]
    apply eq_univ_of_forall
    intro y
    by_cases hy : y ∈ ⋃ i : t,Q i
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hy
      exact Or.inl (hRP (interior_subset ((hQ i).2.2.2 hi)))
    · exact Or.inr hy
  have hMF : ∀ y ∈ M.source ∩ O,(M y : E) = f y := by
    intro y hy
    have hyP : y ∈ interior P := hMs.subset hy.1
    rw [hMval ⟨y,hyP⟩]
    exact hHF ⟨y,hyP⟩ ⟨interior_subset hyP,fun hi =>
      hy.2 (iUnion_mono (fun _ => interior_subset) hi)⟩
  obtain ⟨a,_,hnew,haR,hforward,hreverse⟩ := exists_global_partial_pullback_atlas
    M e he atlas ha f hfPL hrep hO hcover hfront hMF
  have hIR : IsPLIrreducible a R := hIT.of_partial_homeomorph_image haR M
    (hRP.trans hMs.symm.subset) hMT (by
      intro i j
      rw [←hnew j]
      exact haR.compatible i (Sum.inr j))
  exact ⟨Q,t,hQ,htdis,hO,hfront,hOne,a,hIR,hforward,hreverse⟩

end PoincareConjecture.M76

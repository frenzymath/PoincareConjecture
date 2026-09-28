import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.RectangleCoverCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.DiskRimCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.WholeCapRimContact

set_option autoImplicit false
open Set Geometry
open scoped BigOperators
namespace PoincareConjecture.M76.PrismBelt

theorem two_caps_of_actual_rectangular_boundary_cover
    {E F ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [Finite ι] [Finite κ]
    (K : SimplicialComplex ℝ E) {t : Finset E} (ht : t ∈ K.faces) (ht4 : t.card = 4)
    {B S : Set F} (hB : IsFinitePLBallPair (Fin 3 → ℝ) B S)
    (A a : ι → Set F) (hA : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (A i) (a i))
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (M r : κ → Set F) (hM : ∀ j, IsFinitePLBallPair (ℝ × ℝ) (M j) (r j))
    (L q : κ → Bool → Set F) (hL : ∀ j b, IsFinitePLBallPair ℝ (L j b) (q j b))
    (hLM : ∀ j b, L j b ⊆ M j) (hLdis : ∀ j, Disjoint (L j false) (L j true))
    (hcontact : ∀ i, M i ∩ (⋃ j : {j // j ≠ i}, M j) = L i false ∪ L i true)
    (hnoThree : ∀ i j k x, x ∈ M i → x ∈ M j → x ∈ M k → i = j ∨ i = k ∨ j = k)
    (hcover : S = (⋃ i, A i) ∪ (⋃ j, M j))
    (hcapContact : ∀ i, A i ∩ (⋃ j, M j) ⊆ a i) : Nat.card ι = 2 := by
  classical
  let := Fintype.ofFinite ι
  have hAS (i : ι) : A i ⊆ S := fun x hx => hcover.symm.subset (Or.inl (mem_iUnion.mpr ⟨i,hx⟩))
  have hMS (j : κ) : M j ⊆ S := fun x hx => hcover.symm.subset (Or.inr (mem_iUnion.mpr ⟨j,hx⟩))
  have hcap := boundary_caps_whole_rim_contact K ht ht4 hB A a hA hAS hAdis
    (isClosed_iUnion_of_finite fun j => (hM j).isCompact.isClosed) hcover.subset hcapContact
  obtain ⟨_,J,_,_,hJ,hJs⟩ := hB.exists_finite_carrier_and_rim_complexes
  obtain ⟨R₀,U,hR₀,hR₀J,hUR₀,hUs,hdimU,hUzero⟩ :=
    exists_finite_rectangle_cover_count_zero J hJ M r hM L q hL
      (fun j => (hMS j).trans hJs.symm.subset) hLM hLdis hcontact hnoThree
  have hU : U.faces.Finite := hR₀.subset hUR₀
  choose P Q hP hPs hQ hQs using fun i => (hA i).exists_finite_carrier_and_rim_complexes
  let N : (ι × Bool) ⊕ Unit → SimplicialComplex ℝ F :=
    Sum.elim (fun p => if p.2 then P p.1 else Q p.1) (fun _ => U)
  have hN (z : (ι × Bool) ⊕ Unit) : (N z).faces.Finite := by
    cases z with
    | inl p => cases p with | mk i b => cases b <;> first | exact hQ i | exact hP i
    | inr _ => exact hU
  have hNJ (z : (ι × Bool) ⊕ Unit) : (N z).space ⊆ J.space := by
    cases z with
    | inl p =>
      rcases p with ⟨i,b⟩
      cases b
      · exact (hQs i).subset.trans ((hA i).1.trans ((hAS i).trans hJs.symm.subset))
      · exact (hPs i).subset.trans ((hAS i).trans hJs.symm.subset)
    | inr _ => exact hUs.subset.trans ((iUnion_subset hMS).trans hJs.symm.subset)
  obtain ⟨R,C,hR,hRJ,hC⟩ := J.exists_subdivision_with_finite_full_polyhedra hJ N hN hNJ
  let D (i : ι) := C (Sum.inl (i,true))
  let d (i : ι) := C (Sum.inl (i,false))
  let V := C (Sum.inr ())
  have hD (i : ι) : D i ≤ R := (hC (Sum.inl (i,true))).1
  have hd (i : ι) : d i ≤ R := (hC (Sum.inl (i,false))).1
  have hV : V ≤ R := (hC (Sum.inr ())).1
  have hDs (i : ι) : (D i).space = A i := (hC (Sum.inl (i,true))).2.1.trans (hPs i)
  have hds (i : ι) : (d i).space = a i := (hC (Sum.inl (i,false))).2.1.trans (hQs i)
  have hVs : V.space = ⋃ j, M j := (hC (Sum.inr ())).2.1.trans hUs
  have hRs : R.space = S := hRJ.space_eq.trans hJs
  have hRcount := finitePL_ball_boundary_surfaceEulerCount K ht ht4 hB R hR hRs
  have hVzero : V.surfaceEulerCount = 0 :=
    (V.surfaceEulerCount_eq_of_space_eq U (hR.subset hV) hU
      (fun s hs => hRcount.1 s (hV hs)) hdimU (hVs.trans hUs.symm)).trans hUzero
  let G := SimplicialComplex.iUnionOfCompatible D (fun i j s hs t ht =>
    R.inter_subset_convexHull (hD i hs) (hD j ht))
  have hG : G ≤ R := by
    intro s hs
    obtain ⟨i,hi⟩ := mem_iUnion.mp hs
    exact hD i hi
  have hGcount : G.surfaceEulerCount = Nat.card ι := by
    rw [G.surfaceEulerCount_disjoint_family D (fun i => hR.subset (hD i)) rfl]
    · have hc (i : ι) : (D i).surfaceEulerCount = 1 :=
        (finitePL_ball_surfaceEulerCount (hA i) (by simp [Module.finrank_prod])
          (D i) (hR.subset (hD i)) (hDs i)).2
      simp [hc,Nat.card_eq_fintype_card]
    · intro i j hij
      simpa only [hDs] using hAdis hij
  have hpoint (T : SimplicialComplex ℝ F) {s : Finset F} (hs : s ∈ T.faces) :
      (intrinsicInterior ℝ (convexHull ℝ (s : Set F))).Nonempty := by
    obtain ⟨v,hv⟩ := T.nonempty_of_mem_faces hs
    exact (show (convexHull ℝ (s : Set F)).Nonempty from
      ⟨v,subset_convexHull ℝ _ hv⟩).intrinsicInterior (convex_convexHull ℝ _)
  have hfaces : R.faces = G.faces ∪ V.faces := by
    apply Subset.antisymm
    · intro s hs
      obtain ⟨x,hx⟩ := hpoint R hs
      have hxS := hRs.subset (R.convexHull_subset_space hs (intrinsicInterior_subset hx))
      rcases hcover.subset hxS with hxA | hxM
      · obtain ⟨i,hi⟩ := mem_iUnion.mp hxA
        exact Or.inl (mem_iUnion.mpr ⟨i,R.face_mem_subcomplex_of_intrinsicInterior
          (D i) (hD i) hs hx ((hDs i).symm.subset hi)⟩)
      · exact Or.inr (R.face_mem_subcomplex_of_intrinsicInterior V hV hs hx (hVs.symm.subset hxM))
    · exact union_subset hG hV
  have hdD (i : ι) : d i ≤ D i := R.le_of_common_subcomplex_space_subset _ _ (hd i) (hD i)
    ((hds i).subset.trans ((hA i).1.trans (hDs i).symm.subset))
  have hdV (i : ι) : d i ≤ V := R.le_of_common_subcomplex_space_subset _ _ (hd i) hV
    ((hds i).subset.trans (fun x hx => hVs.symm.subset (((hcap i).symm.subset hx).2)))
  have hinter : (G ⊓ V).faces = ⋃ i, (d i).faces := by
    apply Subset.antisymm
    · intro s hs
      change s ∈ G.faces ∧ s ∈ V.faces at hs
      obtain ⟨i,hi⟩ := mem_iUnion.mp hs.1
      obtain ⟨x,hx⟩ := hpoint V hs.2
      have hxa := (hcap i).subset ⟨(hDs i).subset
        ((D i).convexHull_subset_space hi (intrinsicInterior_subset hx)),
        hVs.subset (V.convexHull_subset_space hs.2 (intrinsicInterior_subset hx))⟩
      exact mem_iUnion.mpr ⟨i,R.face_mem_subcomplex_of_intrinsicInterior (d i) (hd i)
        (hV hs.2) hx ((hds i).symm.subset hxa)⟩
    · intro s hs
      obtain ⟨i,hi⟩ := mem_iUnion.mp hs
      exact ⟨mem_iUnion.mpr ⟨i,hdD i hi⟩,hdV i hi⟩
  have hzero : (G ⊓ V).surfaceEulerCount = 0 := by
    rw [(G ⊓ V).surfaceEulerCount_disjoint_family d (fun i => hR.subset (hd i)) hinter]
    · exact Finset.sum_eq_zero (fun i _ => finitePL_disk_rim_surfaceEulerCount (hA i)
        (d i) (hR.subset (hd i)) (hds i))
    · intro i j hij
      rw [hds,hds]
      exact (hAdis hij).mono (hA i).1 (hA j).1
  have heuler := G.surfaceEulerCount_union_add_inter V R (hR.subset hG) (hR.subset hV) hfaces
  rw [hRcount.2,hGcount,hVzero,hzero] at heuler
  omega

end PoincareConjecture.M76.PrismBelt

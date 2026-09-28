import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.BallEulerCount
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.DoubleCoverValuation
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PunctureBallTriangulation
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.Euler.DisjointUnion









set_option autoImplicit false
open Set Geometry
open scoped BigOperators
namespace PoincareConjecture.M76.PrismBelt

theorem exists_finite_rectangle_cover_count_zero
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (M r : ι → Set E) (hM : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (M i) (r i))
    (L q : ι → Bool → Set E) (hL : ∀ i b, IsFinitePLBallPair ℝ (L i b) (q i b))
    (hMK : ∀ i, M i ⊆ K.space) (hLM : ∀ i b, L i b ⊆ M i)
    (hdis : ∀ i, Disjoint (L i false) (L i true))
    (hcontact : ∀ i, M i ∩ (⋃ j : {j // j ≠ i}, M j) = L i false ∪ L i true)
    (hnoThree : ∀ i j k x, x ∈ M i → x ∈ M j → x ∈ M k →
      i = j ∨ i = k ∨ j = k) :
    ∃ R U : SimplicialComplex ℝ E, R.faces.Finite ∧ R.IsSubdivision K ∧
      U ≤ R ∧ U.space = ⋃ i, M i ∧
      (∀ s ∈ U.faces, s.card ≤ 3) ∧ U.surfaceEulerCount = 0 := by
  classical
  let := Fintype.ofFinite ι
  choose A a hA hAM ha har using fun i => (hM i).exists_finite_carrier_and_rim_complexes
  choose B b hB hBL hb hbq using fun i c => (hL i c).exists_finite_carrier_and_rim_complexes
  let J : ι ⊕ (ι × Bool) → SimplicialComplex ℝ E :=
    Sum.elim A (fun p => B p.1 p.2)
  have hJ (i : ι ⊕ (ι × Bool)) : (J i).faces.Finite := by
    cases i with
    | inl i => exact hA i
    | inr p => exact hB p.1 p.2
  have hJK (i : ι ⊕ (ι × Bool)) : (J i).space ⊆ K.space := by
    cases i with
    | inl i => exact (hAM i).subset.trans (hMK i)
    | inr p => exact (hBL p.1 p.2).subset.trans ((hLM p.1 p.2).trans (hMK p.1))
  obtain ⟨R,N,hR,hRK,hN⟩ := K.exists_subdivision_with_finite_full_polyhedra hK J hJ hJK
  let C (i : ι) := N (Sum.inl i)
  let F (i : ι) (b : Bool) := N (Sum.inr (i,b))
  have hC (i : ι) : C i ≤ R := (hN (Sum.inl i)).1
  have hCs (i : ι) : (C i).space = M i := (hN (Sum.inl i)).2.1.trans (hAM i)
  have hF (i : ι) (b : Bool) : F i b ≤ R := (hN (Sum.inr (i,b))).1
  have hFs (i : ι) (b : Bool) : (F i b).space = L i b :=
    (hN (Sum.inr (i,b))).2.1.trans (hBL i b)
  let U := SimplicialComplex.iUnionOfCompatible C (fun i j s hs t ht =>
    R.inter_subset_convexHull (hC i hs) (hC j ht))
  let D (i : ι) := SimplicialComplex.iUnionOfCompatible (F i) (fun b c s hs t ht =>
    R.inter_subset_convexHull (hF i b hs) (hF i c ht))
  have hUR : U ≤ R := by
    intro s hs
    obtain ⟨i,hi⟩ := mem_iUnion.mp hs
    exact hC i hi
  have hDR (i : ι) : D i ≤ R := by
    intro s hs
    obtain ⟨b,hb⟩ := mem_iUnion.mp hs
    exact hF i b hb
  have hUs : U.space = ⋃ i, M i := by
    rw [SimplicialComplex.space_iUnionOfCompatible]
    simp_rw [hCs]
  have hDs (i : ι) : (D i).space = L i false ∪ L i true := by
    rw [SimplicialComplex.space_iUnionOfCompatible]
    simp only [hFs]
    ext x
    simp only [mem_iUnion,mem_union,Bool.exists_bool]
  have hCcount (i : ι) := finitePL_ball_surfaceEulerCount (hM i)
    (by simp [Module.finrank_prod]) (C i) (hR.subset (hC i)) (hCs i)
  have hDcount (i : ι) : (D i).surfaceEulerCount = 2 := by
    rw [(D i).surfaceEulerCount_disjoint_family (F i) (fun b => hR.subset (hF i b)) rfl]
    · have hc (b : Bool) : (F i b).surfaceEulerCount = 1 :=
        (finitePL_ball_surfaceEulerCount (hL i b) (by simp) (F i b)
          (hR.subset (hF i b)) (hFs i b)).2
      simp [hc]
    · intro b c hbc
      simp only [hFs]
      cases b <;> cases c
      · exact (hbc rfl).elim
      · exact hdis i
      · exact (hdis i).symm
      · exact (hbc rfl).elim
  have hpoint (T : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ T.faces) :
      (intrinsicInterior ℝ (convexHull ℝ (s : Set E))).Nonempty := by
    obtain ⟨v,hv⟩ := T.nonempty_of_mem_faces hs
    exact (show (convexHull ℝ (s : Set E)).Nonempty from
      ⟨v,subset_convexHull ℝ _ hv⟩).intrinsicInterior (convex_convexHull ℝ _)
  have hDc (i : ι) (s : Finset E) : s ∈ (D i).faces ↔
      s ∈ (C i).faces ∧ ∃ j, j ≠ i ∧ s ∈ (C j).faces := by
    constructor
    · intro hs
      obtain ⟨x,hx⟩ := hpoint (D i) hs
      have hxD := (D i).convexHull_subset_space hs (intrinsicInterior_subset hx)
      rw [hDs,←hcontact i] at hxD
      obtain ⟨j,hj⟩ := mem_iUnion.mp hxD.2
      exact ⟨R.face_mem_subcomplex_of_intrinsicInterior (C i) (hC i) (hDR i hs)
        hx ((hCs i).symm.subset hxD.1),j,j.2,
        R.face_mem_subcomplex_of_intrinsicInterior (C j) (hC j) (hDR i hs)
          hx ((hCs j).symm.subset hj)⟩
    · rintro ⟨hi,j,hji,hj⟩
      obtain ⟨x,hx⟩ := hpoint (C i) hi
      have hxD : x ∈ (D i).space := by
        rw [hDs,←hcontact i]
        exact ⟨(hCs i).subset ((C i).convexHull_subset_space hi (intrinsicInterior_subset hx)),
          mem_iUnion.mpr ⟨⟨j,hji⟩,(hCs j).subset
            ((C j).convexHull_subset_space hj (intrinsicInterior_subset hx))⟩⟩
      exact R.face_mem_subcomplex_of_intrinsicInterior (D i) (hDR i) (hC i hi) hx hxD
  have hcount := surfaceEulerCount_double_cover U (hR.subset hUR) C D
    (fun i s hs => mem_iUnion.mpr ⟨i,hs⟩) (fun _ hs => mem_iUnion.mp hs) hDc
    (by
      intro s hs i j k hi hj hk
      obtain ⟨x,hx⟩ := hpoint U hs
      exact hnoThree i j k x
        ((hCs i).subset ((C i).convexHull_subset_space hi (intrinsicInterior_subset hx)))
        ((hCs j).subset ((C j).convexHull_subset_space hj (intrinsicInterior_subset hx)))
        ((hCs k).subset ((C k).convexHull_subset_space hk (intrinsicInterior_subset hx))))
  have hzero : U.surfaceEulerCount = 0 := by
    simp only [fun i => (hCcount i).2,hDcount,mul_one,sub_self,Finset.sum_const_zero] at hcount
    omega
  refine ⟨R,U,hR,hRK,hUR,hUs,?_,hzero⟩
  intro s hs
  obtain ⟨i,hi⟩ := mem_iUnion.mp hs
  exact (hCcount i).1 s hi

end PoincareConjecture.M76.PrismBelt

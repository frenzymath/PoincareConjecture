import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.BoundaryCount.RectangleCoverCount
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.SharedBoundaryConeUnion



set_option autoImplicit false
open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks
open PrismBelt

theorem exists_three_disk_four_arc_neighborhood_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (M m : Option Bool → Set E)
    (hM : ∀ i, IsFinitePLBallPair (ℝ × ℝ) (M i) (m i))
    (L l : Bool → Bool → Set E)
    (hL : ∀ i b, IsFinitePLBallPair ℝ (L i b) (l i b))
    (hMK : ∀ i, M i ⊆ K.space)
    (hcontact : ∀ b, M none ∩ M (some b) = L b false ∪ L b true)
    (hLdis : ∀ b, Disjoint (L b false) (L b true))
    (hMdis : Disjoint (M (some false)) (M (some true))) :
    ∃ R N : SimplicialComplex ℝ E, R.faces.Finite ∧ R.IsSubdivision K ∧
      N ≤ R ∧ N.space = M none ∪ (M (some false) ∪ M (some true)) ∧
      (∀ s ∈ N.faces, s.card ≤ 3) ∧ N.surfaceEulerCount = -1 := by
  classical
  choose A a hA hAM ha ham using fun i => (hM i).exists_finite_carrier_and_rim_complexes
  choose B b hB hBL hb hbl using fun i c => (hL i c).exists_finite_carrier_and_rim_complexes
  let J : Option Bool ⊕ (Bool × Bool) → SimplicialComplex ℝ E :=
    Sum.elim A (fun p => B p.1 p.2)
  have hJ (i : Option Bool ⊕ (Bool × Bool)) : (J i).faces.Finite := by
    cases i with
    | inl i => exact hA i
    | inr p => exact hB p.1 p.2
  have hLK (i b : Bool) : L i b ⊆ K.space := by
    intro x hx
    apply hMK none
    apply ((hcontact i).symm.subset ?_).1
    cases b
    · exact Or.inl hx
    · exact Or.inr hx
  have hJK (i : Option Bool ⊕ (Bool × Bool)) : (J i).space ⊆ K.space := by
    cases i with
    | inl i => exact (hAM i).subset.trans (hMK i)
    | inr p => exact (hBL p.1 p.2).subset.trans (hLK p.1 p.2)
  obtain ⟨R,C,hR,hRK,hC⟩ := K.exists_subdivision_with_finite_polyhedra hK J hJ hJK
  let D (i : Option Bool) := C (Sum.inl i)
  let F (i b : Bool) := C (Sum.inr (i,b))
  have hD (i : Option Bool) : D i ≤ R := (hC (Sum.inl i)).1
  have hDs (i : Option Bool) : (D i).space = M i := (hC (Sum.inl i)).2.trans (hAM i)
  have hF (i b : Bool) : F i b ≤ R := (hC (Sum.inr (i,b))).1
  have hFs (i b : Bool) : (F i b).space = L i b :=
    (hC (Sum.inr (i,b))).2.trans (hBL i b)
  let T (i : Bool) := (F i false).unionOfCompatible (F i true)
    (fun _ hs _ ht => R.inter_subset_convexHull (hF i false hs) (hF i true ht))
  have hT (i : Bool) : T i ≤ R := fun _ hs => hs.elim (fun hs => hF i false hs) (fun hs => hF i true hs)
  have hTs (i : Bool) : (T i).space = L i false ∪ L i true := by
    rw [SimplicialComplex.space_unionOfCompatible, hFs, hFs]
  have hTc (i : Bool) : (T i).surfaceEulerCount = 2 := by
    have hcount := (F i false).surfaceEulerCount_union_add_inter (F i true) (T i)
      (hR.subset (hF i false)) (hR.subset (hF i true)) rfl
    have hcountF (b : Bool) : (F i b).surfaceEulerCount = 1 :=
      (finitePL_ball_surfaceEulerCount (hL i b) (by simp) (F i b)
        (hR.subset (hF i b)) (hFs i b)).2
    have hempty : (F i false ⊓ F i true).space = ∅ := by
      rw [space_inf_eq_inter_of_le R _ _ (hF i false) (hF i true), hFs,hFs]
      exact (hLdis i).eq_bot
    rw [hcountF,hcountF,(F i false ⊓ F i true).surfaceEulerCount_eq_zero_of_space_empty hempty] at hcount
    omega
  have hDT (i : Bool) : D none ⊓ D (some i) = T i := by
    have hs : (D none ⊓ D (some i)).space = (T i).space := by
      rw [space_inf_eq_inter_of_le R _ _ (hD none) (hD (some i)),
        hDs,hDs,hTs,hcontact]
    exact le_antisymm
      (R.le_of_common_subcomplex_space_subset _ _ (inf_le_left.trans (hD none)) (hT i) hs.subset)
      (R.le_of_common_subcomplex_space_subset _ _ (hT i) (inf_le_left.trans (hD none)) hs.symm.subset)
  let U := (D none).unionOfCompatible (D (some false))
    (fun _ hs _ ht => R.inter_subset_convexHull (hD none hs) (hD (some false) ht))
  have hU : U ≤ R := fun _ hs => hs.elim (fun hs => hD none hs) (fun hs => hD (some false) hs)
  have hUs : U.space = M none ∪ M (some false) := by
    rw [SimplicialComplex.space_unionOfCompatible,hDs,hDs]
  let N := U.unionOfCompatible (D (some true))
    (fun _ hs _ ht => R.inter_subset_convexHull (hU hs) (hD (some true) ht))
  have hN : N ≤ R := fun _ hs => hs.elim (fun hs => hU hs) (fun hs => hD (some true) hs)
  have hNs : N.space = M none ∪ (M (some false) ∪ M (some true)) := by
    rw [SimplicialComplex.space_unionOfCompatible,hUs,hDs,union_assoc]
  have hUT : U ⊓ D (some true) = T true := by
    have hs : (U ⊓ D (some true)).space = (T true).space := by
      rw [space_inf_eq_inter_of_le R _ _ hU (hD (some true)),
        hUs,hDs,union_inter_distrib_right,Set.disjoint_iff_inter_eq_empty.mp hMdis,
        union_empty,hcontact,hTs]
    exact le_antisymm
      (R.le_of_common_subcomplex_space_subset _ _ (inf_le_left.trans hU) (hT true) hs.subset)
      (R.le_of_common_subcomplex_space_subset _ _ (hT true) (inf_le_left.trans hU) hs.symm.subset)
  have hDcount (i : Option Bool) := finitePL_ball_surfaceEulerCount (hM i)
    (by simp [Module.finrank_prod]) (D i) (hR.subset (hD i)) (hDs i)
  have hUc := (D none).surfaceEulerCount_union_add_inter (D (some false)) U
    (hR.subset (hD none)) (hR.subset (hD (some false))) rfl
  have hNc := U.surfaceEulerCount_union_add_inter (D (some true)) N
    (hR.subset hU) (hR.subset (hD (some true))) rfl
  rw [hDT,hTc,(hDcount none).2,(hDcount (some false)).2] at hUc
  rw [hUT,hTc,(hDcount (some true)).2] at hNc
  refine ⟨R,N,hR,hRK,hN,hNs,?_,by omega⟩
  intro s hs
  rcases hs with (hs | hs) | hs
  · exact (hDcount none).1 s hs
  · exact (hDcount (some false)).1 s hs
  · exact (hDcount (some true)).1 s hs

end PoincareConjecture.M76.Dehn.Annuli.ProductEndDisks

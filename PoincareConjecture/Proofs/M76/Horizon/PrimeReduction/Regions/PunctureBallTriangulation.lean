import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPairs
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.PuncturedSubcomplex

set_option autoImplicit false
open Set Geometry

namespace Set

theorem IsFinitePLBallPair.exists_finite_carrier_and_rim_complexes
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {a r : Set X} (ha : IsFinitePLBallPair V a r) :
    ∃ K L : SimplicialComplex ℝ X,
      K.faces.Finite ∧ K.space = a ∧ L.faces.Finite ∧ L.space = r := by
  obtain ⟨hra, c, hc, hcv, hne, e, he, hr⟩ := ha
  have hecopy := he
  obtain ⟨f, ⟨K, hK, hKa, hf⟩, heval⟩ := hecopy
  have hi := he.symm
  have hicopy := hi
  obtain ⟨g, ⟨J, hJ, hJc, hg⟩, hival⟩ := hicopy
  have hfront := J.frontierSubcomplex_space hc.isClosed hcv hne hJc
  have hmem (y : c) : (y : V) ∈ frontier c ↔ (e.symm y : X) ∈ r := by
    simpa only [e.apply_symm_apply] using (hr (e.symm y)).symm
  have hR := hi.restrictSubsets hc.isClosed.frontier_subset hra hmem
    (J.frontierSubcomplex c) (J.frontierSubcomplex_finite c hJ) hfront
  obtain ⟨_, ⟨L, hL, hLr, _⟩, _⟩ := hR.symm
  exact ⟨K, L, hK, hKa, hL, hLr⟩

end Set

namespace Geometry.SimplicialComplex

theorem exists_subdivision_with_finite_ball_pairs
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [Finite ι]
    (K : SimplicialComplex ℝ X) (hK : K.faces.Finite)
    (a r : ι → Set X) (ha : ∀ i, IsFinitePLBallPair V (a i) (r i))
    (haK : ∀ i, a i ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ X) (A B : ι → SimplicialComplex ℝ X),
      R.faces.Finite ∧ R.IsSubdivision K ∧ R.space = K.space ∧
      ∀ i, A i ≤ R ∧ B i ≤ A i ∧
        (A i).faces.Finite ∧ (B i).faces.Finite ∧
        (A i).space = a i ∧ (B i).space = r i ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (A i).vertices) → s ∈ (A i).faces) ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (B i).vertices) → s ∈ (B i).faces) := by
  classical
  choose J L hJ hJa hL hLr using fun i => (ha i).exists_finite_carrier_and_rim_complexes
  let T : ι × Bool → SimplicialComplex ℝ X := fun j => if j.2 then J j.1 else L j.1
  have hT (j : ι × Bool) : (T j).faces.Finite := by
    rcases j with ⟨i, b⟩
    cases b
    · exact hL i
    · exact hJ i
  have hTK (j : ι × Bool) : (T j).space ⊆ K.space := by
    rcases j with ⟨i, b⟩
    cases b
    · exact (hLr i).subset.trans ((ha i).1.trans (haK i))
    · exact (hJa i).subset.trans (haK i)
  obtain ⟨R, C, hR, hRK, hC⟩ :=
    K.exists_subdivision_with_finite_full_polyhedra hK T hT hTK
  have hCa (i : ι) : (C (i, true)).space = a i :=
    (hC (i, true)).2.1.trans (hJa i)
  have hCr (i : ι) : (C (i, false)).space = r i :=
    (hC (i, false)).2.1.trans (hLr i)
  refine ⟨R, (fun i => C (i, true)), (fun i => C (i, false)), hR, hRK,
    hRK.space_eq, ?_⟩
  intro i
  have hBA : C (i, false) ≤ C (i, true) :=
    R.le_of_common_subcomplex_space_subset _ _ (hC (i, false)).1 (hC (i, true)).1
      ((hCr i).subset.trans ((ha i).1.trans (hCa i).symm.subset))
  exact ⟨(hC (i, true)).1, hBA, hR.subset (hC (i, true)).1,
    hR.subset (hC (i, false)).1, hCa i, hCr i,
    (hC (i, true)).2.2, (hC (i, false)).2.2⟩

theorem exists_finite_closed_punctured_ball_carrier
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [Finite ι]
    (K : SimplicialComplex ℝ X) (hK : K.faces.Finite)
    (a r : ι → Set X) (ha : ∀ i, IsFinitePLBallPair V (a i) (r i))
    (haK : ∀ i, a i ⊆ K.space)
    (hdis : Pairwise fun i j => Disjoint (a i) (a j))
    (hclosed : IsClosed (K.space \ ⋃ i, a i \ r i)) :
    ∃ (R P : SimplicialComplex ℝ X) (A B : ι → SimplicialComplex ℝ X),
      R.faces.Finite ∧ R.IsSubdivision K ∧ P ≤ R ∧ P.faces.Finite ∧
      P.space = K.space \ ⋃ i, a i \ r i ∧
      (∀ i, A i ≤ R ∧ B i ≤ A i ∧ B i ≤ P ∧
        (A i).space = a i ∧ (B i).space = r i) ∧
      ∀ J : SimplicialComplex ℝ X, J ≤ R →
        J.space ⊆ K.space \ ⋃ i, a i \ r i → J ≤ P := by
  obtain ⟨R, A, B, hR, hRK, hRs, hAB⟩ :=
    K.exists_subdivision_with_finite_ball_pairs hK a r ha haK
  have hrem : R.space \ ⋃ i, (A i).space \ (B i).space =
      K.space \ ⋃ i, a i \ r i := by
    simp only [hRs, fun i => (hAB i).2.2.2.2.1, fun i => (hAB i).2.2.2.2.2.1]
  obtain ⟨P, hPR, hP, hPs, hkeep⟩ :=
    R.exists_closed_punctured_subcomplex hR A B (fun i => (hAB i).1)
      (fun i => (hAB i).2.1.trans (hAB i).1) (hrem.symm ▸ hclosed)
  have hrkeep (i : ι) : r i ⊆ K.space \ ⋃ j, a j \ r j := by
    intro x hx
    refine ⟨haK i ((ha i).1 hx), ?_⟩
    intro hxholes
    obtain ⟨j, hxj, hxr⟩ := mem_iUnion.mp hxholes
    by_cases hij : i = j
    · exact hxr (hij ▸ hx)
    · exact disjoint_left.mp (hdis hij) ((ha i).1 hx) hxj
  refine ⟨R, P, A, B, hR, hRK, hPR, hP, hPs.trans hrem, ?_, ?_⟩
  · intro i
    refine ⟨(hAB i).1, (hAB i).2.1, ?_,
      (hAB i).2.2.2.2.1, (hAB i).2.2.2.2.2.1⟩
    exact hkeep (B i) ((hAB i).2.1.trans (hAB i).1)
      (((hAB i).2.2.2.2.2.1.subset.trans (hrkeep i)).trans hrem.symm.subset)
  · intro J hJR hJp
    exact hkeep J hJR (hJp.trans hrem.symm.subset)

theorem exists_finite_punctured_ambient_ball_carrier
    {V X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [Finite ι]
    (hdim : Module.finrank ℝ V = Module.finrank ℝ X)
    (K : SimplicialComplex ℝ X) (hK : K.faces.Finite)
    (a r : ι → Set X) (ha : ∀ i, IsFinitePLBallPair V (a i) (r i))
    (haK : ∀ i, a i ⊆ K.space)
    (hdis : Pairwise fun i j => Disjoint (a i) (a j)) :
    ∃ (R P : SimplicialComplex ℝ X) (A B : ι → SimplicialComplex ℝ X),
      R.faces.Finite ∧ R.IsSubdivision K ∧ P ≤ R ∧ P.faces.Finite ∧
      P.space = K.space \ ⋃ i, a i \ r i ∧
      (∀ i, A i ≤ R ∧ B i ≤ A i ∧ B i ≤ P ∧
        (A i).space = a i ∧ (B i).space = r i) ∧
      ∀ J : SimplicialComplex ℝ X, J ≤ R →
        J.space ⊆ K.space \ ⋃ i, a i \ r i → J ≤ P := by
  have hopen : IsOpen (⋃ i, a i \ r i) := isOpen_iUnion fun i => by
    rw [← (ha i).interior_eq_sdiff_of_finrank_eq hdim]
    exact isOpen_interior
  exact K.exists_finite_closed_punctured_ball_carrier hK a r ha haK hdis
    ((K.isCompact_space_of_finite hK).isClosed.sdiff hopen)

end Geometry.SimplicialComplex

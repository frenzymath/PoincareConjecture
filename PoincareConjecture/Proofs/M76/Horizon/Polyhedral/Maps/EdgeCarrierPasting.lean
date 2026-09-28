import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Maps.SourceEdgeHomotopy
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Maps.FiniteSubcomplexHomotopyGluing
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.CommonSubcomplexUnion
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.EdgeIntersections










set_option autoImplicit false

open Set unitInterval

namespace Geometry.SimplicialComplex

theorem exists_edge_carrier_pasting
    {E X V ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [Nonempty X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Finite κ]
    (e : ι → OpenPartialHomeomorph X V)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V)
    (K : SimplicialComplex ℝ E) (a b : κ → K.vertices)
    (hab : ∀ k, (a k : E) ≠ b k)
    (hedge : ∀ k, {(a k : E), (b k : E)} ∈ K.faces)
    (hinj : Function.Injective (fun k => ({(a k : E), (b k : E)} : Finset E)))
    (f : E → X) (p : K.vertices → C(I, X)) (H : κ → C(I × I, X))
    (hend : ∀ k t, H k (t, 0) = p (a k) t ∧ H k (t, 1) = p (b k) t)
    (hstart : ∀ k (s : I), H k (0, s) = f (AffineMap.lineMap (a k : E) (b k : E) (s : ℝ)))
    (q : κ → ℝ → X) (hfinal : ∀ k s, H k (1, s) = q k s)
    (hq : ∀ k, PolyhedralPLInCharts e (q k) (Icc 0 1)) :
    ∃ (T : SimplicialComplex ℝ E) (G : C(I × T.space, X)) (g : E → X),
      T.faces.Finite ∧ T ≤ K ∧
      T.space = ⋃ k, segment ℝ (a k : E) (b k : E) ∧
      (∀ k (t s : I) (hx : AffineMap.lineMap (a k : E) (b k : E) (s : ℝ) ∈ T.space),
        G (t, ⟨AffineMap.lineMap (a k : E) (b k : E) (s : ℝ), hx⟩) = H k (t, s)) ∧
      (∀ x : T.space, G (0, x) = f x) ∧
      (∀ x : T.space, G (1, x) = g x) ∧ PolyhedralPLInCharts e g T.space := by
  classical
  choose J l D hJ hJK hJS hla hlb hline hmap hinv hD hD0 hD1 hPL using
    fun k => K.exists_edge_homotopy_transport (hab k) (hedge k) (H k) (hq k) (hfinal k)
  have hcross : ∀ i j, ∀ s ∈ (J i).faces, ∀ t ∈ (J j).faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) := by
    intro i j s hs t ht
    exact K.inter_subset_convexHull (hJK i hs) (hJK j ht)
  let T := iUnionOfCompatible J hcross
  have hT : T.faces.Finite := finite_faces_iUnionOfCompatible J hcross hJ
  have hJT : ∀ k, J k ≤ T := le_iUnionOfCompatible J hcross
  have hTK : T ≤ K := by
    intro s hs
    obtain ⟨k, hk⟩ := mem_iUnion.mp hs
    exact hJK k hk
  have hTS : T.space = ⋃ k, (J k).space := space_iUnionOfCompatible J hcross
  have hvertex (k : κ) (t : I) (x : (J k).space) (v : K.vertices)
      (hxv : (x : E) = v) (hv : v = a k ∨ v = b k) : D k (t, x) = p v t := by
    rcases hv with rfl | rfl
    · exact (hD k t x 0 (by simpa using hxv)).trans (hend k t).1
    · exact (hD k t x 1 (by simpa using hxv)).trans (hend k t).2
  have hagree : ∀ i j (t : I) (x : E) (hi : x ∈ (J i).space) (hj : x ∈ (J j).space),
      D i (t, ⟨x, hi⟩) = D j (t, ⟨x, hj⟩) := by
    intro i j t x hi hj
    by_cases hij : i = j
    · subst j
      rfl
    have hpairs : ({(a i : E), (b i : E)} : Finset E) ≠ {(a j : E), (b j : E)} :=
      fun h => hij (hinj h)
    have hx := K.mem_segment_inter_of_distinct_edges (hedge i) (hedge j) hpairs
      (show x ∈ segment ℝ (a i : E) (b i : E) ∩ segment ℝ (a j : E) (b j : E) from
        ⟨(hJS i).subset hi, (hJS j).subset hj⟩)
    have hxK : x ∈ K.vertices := by
      rcases hx.1 with rfl | rfl
      · exact (a i).property
      · exact (b i).property
    let v : K.vertices := ⟨x, hxK⟩
    have hvi : v = a i ∨ v = b i := hx.1.imp Subtype.ext Subtype.ext
    have hvj : v = a j ∨ v = b j := hx.2.imp Subtype.ext Subtype.ext
    exact (hvertex i t ⟨x, hi⟩ v rfl hvi).trans (hvertex j t ⟨x, hj⟩ v rfl hvj).symm
  obtain ⟨G, g, hG, hG1, hg, hgPL⟩ :=
    T.exists_polyhedralPL_homotopy_of_finite_subcomplex_cover e hcover hcompat hT J hJT
      hTS.subset D hagree (fun k => q k ∘ l k) hPL hD1
  refine ⟨T, G, g, hT, hTK, ?_, ?_, ?_, hG1, hgPL⟩
  · simpa only [hJS] using hTS
  · intro k t s hx
    have hxs : AffineMap.lineMap (a k : E) (b k : E) (s : ℝ) ∈ (J k).space :=
      (hJS k).symm.subset (lineMap_mem_segment ℝ _ _ s.property)
    exact (hG k t ⟨_, hxs⟩).trans (hD k t ⟨_, hxs⟩ s rfl)
  · intro x
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hTS.subset x.property)
    exact (hG k 0 ⟨x, hk⟩).trans (hD0 k f (hstart k) ⟨x, hk⟩)

end Geometry.SimplicialComplex

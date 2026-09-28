import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.LeafFields.OriginalTriangleEdgeGerm
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)







theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_graph
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q)) :
    ∃ (B : OpenPartialHomeomorph X V3) (z : V3) (r : ℝ)
      (N J : SimplicialComplex ℝ V3),
      (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
      y ∈ B.source ∧ z ≠ B y ∧ 0 < r ∧ r < dist (B y) z ∧
      Metric.ball (B y) r ⊆ B.target ∧
      (B '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ B.source)) ∩
          Metric.ball (B y) r =
        AffineMap.lineMap (B y) z '' Ico (0 : ℝ) (r / dist (B y) z) ∧
      N.faces.Finite ∧ IsCompact N.space ∧ IsClosed N.space ∧
      B y ∈ interior N.space ∧ N.space ⊆ Metric.ball (B y) r ∧
      J.faces.Finite ∧ B y ∈ J.space ∧
      J.space =
        (B '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ B.source)) ∩ N.space ∧
      J.space = segment ℝ (B y) z ∩ N.space ∧
      ∀ a ∈ J.faces, a.card ≤ 2 := by
  classical
  obtain ⟨B, z, r, hB, hyB, hzy, hr, hrdist, hballB, hsection, _, _⟩ :=
    h.exists_triangle_halfInterval hgi hSV hpq hwp hwq ht hy
  obtain ⟨N, hN, hyN, hNball⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      (isCompact_singleton (x := B y)) Metric.isOpen_ball
      (singleton_subset_iff.mpr (Metric.mem_ball_self hr))
  have hyN' : B y ∈ interior N.space := hyN (mem_singleton (B y))
  have hcompact : IsCompact N.space := N.isCompact_space_of_finite hN
  have hdist : 0 < dist (B y) z := dist_pos.mpr hzy.symm
  have hlocal :
      (B '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ B.source)) ∩ N.space =
        segment ℝ (B y) z ∩ N.space := by
    ext x
    constructor
    · rintro ⟨hx, hxN⟩
      obtain ⟨t, htpar, rfl⟩ := hsection.subset ⟨hx, hNball hxN⟩
      exact ⟨lineMap_mem_segment ℝ (B y) z
        ⟨htpar.1, (htpar.2.trans ((div_lt_one hdist).mpr hrdist)).le⟩, hxN⟩
    · rintro ⟨hxseg, hxN⟩
      rw [segment_eq_image_lineMap] at hxseg
      obtain ⟨t, htpar, rfl⟩ := hxseg
      have htbound : t < r / dist (B y) z := by
        apply (lt_div_iff₀ hdist).mpr
        simpa only [Metric.mem_ball, dist_lineMap_left, Real.norm_eq_abs,
          abs_of_nonneg htpar.1] using hNball hxN
      exact ⟨(hsection.symm.subset ⟨t, ⟨htpar.1, htbound⟩, rfl⟩).1, hxN⟩
  obtain ⟨T, hT, hTs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_finiteHull
    (fun _ : Unit => ({B y, z} : Finset V3))
  have hTspace : T.space = segment ℝ (B y) z := by
    simpa only [iUnion_const, Finset.coe_pair, convexHull_pair] using hTs
  obtain ⟨J, hJ, hJs⟩ := T.exists_finite_triangulation_inter N hT hN
  rw [hTspace] at hJs
  have hyJ : B y ∈ J.space := hJs.symm.subset
    ⟨left_mem_segment ℝ (B y) z, interior_subset hyN'⟩
  let A : AffineSubspace ℝ V3 := affineSpan ℝ ({B y, z} : Set V3)
  have hAdim : Module.finrank ℝ A.direction ≤ 1 := by
    change Module.finrank ℝ (affineSpan ℝ ({B y, z} : Set V3)).direction ≤ 1
    rw [direction_affineSpan]
    exact (collinear_pair ℝ (B y) z).finrank_le_one
  have hcover : ∀ x ∈ J.space, ∃ L ∈ ({A} : Finset (AffineSubspace ℝ V3)), x ∈ L := by
    intro x hx
    have hxlocal := hlocal.symm.subset (hJs.subset hx)
    obtain ⟨t, _, rfl⟩ := hsection.subset ⟨hxlocal.1, hNball hxlocal.2⟩
    exact ⟨A, Finset.mem_singleton_self A, AffineMap.lineMap_mem_affineSpan_pair _ _ _⟩
  refine ⟨B, z, r, N, J, hB, hyB, hzy, hr, hrdist, hballB, hsection,
    hN, hcompact, hcompact.isClosed, hyN', hNball, hJ, hyJ,
    hJs.trans hlocal.symm, hJs, ?_⟩
  intro a ha
  exact J.face_card_le_of_finite_affine_cover {A}
    (by intro L hL; rcases Finset.mem_singleton.mp hL with rfl; exact hAdim) hcover ha

end PoincareConjecture.M76

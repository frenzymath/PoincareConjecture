import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.MeshTransport









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section

open Classical

namespace PoincareConjecture.Topology.Surface



theorem affineBasis_cutPoints_ne
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) :
    affineCutPoint f (b 0) (b 1) ≠ affineCutPoint f (b 0) (b 2) := by
  intro h
  have hc := congrArg (b.coord 1) h
  norm_num [affineCutPoint, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
    b.coord_apply, Fin.ext_iff] at hc
  rcases hc with hc | hc <;> linarith



theorem affineBasis_cutPoint_geometry
    (b : AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ)
    (h0 : 0 < f (b 0)) (h1 : f (b 1) < 0) :
    let q := affineCutPoint f (b 0) (b 1)
    q ∈ frontier (convexHull ℝ (range b)) ∧ q ∉ range b ∧ f q = 0 := by
  dsimp only
  refine ⟨?_, ?_, affineCutPoint.apply_eq_zero f _ _ h0 h1⟩
  · rw [frontier_convexHull_affineBasis_fin3_segments]
    refine mem_iUnion.mpr ⟨2, ?_⟩
    change affineCutPoint f (b 0) (b 1) ∈ affineSegment ℝ (b 0) (b 1)
    rw [affineSegment_eq_segment]
    exact affineCutPoint.mem_segment f _ _ h0 h1
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact affineCutPoint.ne_left f _ _ h0 h1 hk.symm
    · exact affineCutPoint.ne_right f _ _ h0 h1 hk.symm
    · have hc := congrArg (b.coord 2) hk
      norm_num [affineCutPoint, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring,
        b.coord_apply, Fin.ext_iff] at hc


def localRefinementBoundaryCuts (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (t : M.Triangle) :
    List (EuclideanSpace ℝ (Fin 2)) :=
  if hp : Nonempty (M.PositiveStrictOrdering f t) then
    let o := Classical.choice hp
    [affineCutPoint f (M.position (M.orderedVertex t (o.perm 0)))
      (M.position (M.orderedVertex t (o.perm 1))),
     affineCutPoint f (M.position (M.orderedVertex t (o.perm 0)))
      (M.position (M.orderedVertex t (o.perm 2)))]
  else if hn : Nonempty (M.NegativeStrictOrdering f t) then
    let o := Classical.choice hn
    [affineCutPoint f (M.position (M.orderedVertex t (o.perm 0)))
      (M.position (M.orderedVertex t (o.perm 1))),
     affineCutPoint f (M.position (M.orderedVertex t (o.perm 0)))
      (M.position (M.orderedVertex t (o.perm 2)))]
  else if hep : Nonempty (M.PositiveEdgeOrdering f t) then
    let o := Classical.choice hep
    [affineCutPoint f (M.position (M.orderedVertex t (o.perm 0)))
      (M.position (M.orderedVertex t (o.perm 1)))]
  else if hen : Nonempty (M.NegativeEdgeOrdering f t) then
    let o := Classical.choice hen
    [affineCutPoint f (M.position (M.orderedVertex t (o.perm 0)))
      (M.position (M.orderedVertex t (o.perm 1)))]
  else []


theorem localRefinementBoundaryCuts_nodup (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (t : M.Triangle) :
    (localRefinementBoundaryCuts M f t).Nodup := by
  unfold localRefinementBoundaryCuts
  split_ifs with hp hn hep hen
  · let o := Classical.choice hp
    have h := affineBasis_cutPoints_ne
      (affineBasisOfTriangle (M.position ∘ M.orderedVertex t ∘ o.perm)
        (M.orderedVertex_perm_affineIndependent t o.perm)) f o.positive o.negative_one
    change affineCutPoint f (M.position (M.orderedVertex t (o.perm 0)))
      (M.position (M.orderedVertex t (o.perm 1))) ≠
      affineCutPoint f (M.position (M.orderedVertex t (o.perm 0)))
        (M.position (M.orderedVertex t (o.perm 2))) at h
    simpa [o] using h
  · let o := Classical.choice hn
    have h := affineBasis_cutPoints_ne
      (affineBasisOfTriangle (M.position ∘ M.orderedVertex t ∘ o.perm)
        (M.orderedVertex_perm_affineIndependent t o.perm)) (-f)
      (by
        change 0 < -(f (M.position (M.orderedVertex t (o.perm 0))))
        exact neg_pos.mpr o.negative)
      (by
        change -(f (M.position (M.orderedVertex t (o.perm 1)))) < 0
        exact neg_neg_of_pos o.positive_one)
    change affineCutPoint (-f) (M.position (M.orderedVertex t (o.perm 0)))
      (M.position (M.orderedVertex t (o.perm 1))) ≠
      affineCutPoint (-f) (M.position (M.orderedVertex t (o.perm 0)))
        (M.position (M.orderedVertex t (o.perm 2))) at h
    simpa [o, affineCutPoint.neg] using h
  · exact List.nodup_singleton _
  · exact List.nodup_singleton _
  · exact List.nodup_nil

private theorem ordered_cut_geometry (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (t : M.Triangle) (e : Equiv.Perm (Fin 3))
    (hcross : f (M.position (M.orderedVertex t (e 0))) *
      f (M.position (M.orderedVertex t (e 1))) < 0) :
    let q := affineCutPoint f (M.position (M.orderedVertex t (e 0)))
      (M.position (M.orderedVertex t (e 1)))
    q ∈ frontier (convexHull ℝ (range (meshTriangleBasis M t))) ∧
      q ∉ range (meshTriangleBasis M t) ∧ f q = 0 := by
  let b := affineBasisOfTriangle (M.position ∘ M.orderedVertex t ∘ e)
    (M.orderedVertex_perm_affineIndependent t e)
  have hr : range b = range (meshTriangleBasis M t) := by
    rw [range_meshTriangleBasis]
    exact M.range_orderedVertex_perm t e
  rcases mul_neg_iff.mp hcross with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have h := affineBasis_cutPoint_geometry b f h0 h1
    dsimp only at h
    rw [hr] at h
    exact h
  · have hn0 : 0 < (-f) (b 0) := neg_pos.mpr h0
    have hn1 : (-f) (b 1) < 0 := neg_neg_of_pos h1
    have h := affineBasis_cutPoint_geometry b (-f) hn0 hn1
    dsimp only at h
    rw [hr] at h
    simp only [affineCutPoint.neg, AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] at h
    exact h



theorem localRefinementBoundaryCuts_geometry (M : TriangleMesh)
    (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (t : M.Triangle)
    {q : EuclideanSpace ℝ (Fin 2)} (hq : q ∈ localRefinementBoundaryCuts M f t) :
    q ∈ frontier (convexHull ℝ (range (meshTriangleBasis M t))) ∧
      q ∉ range (meshTriangleBasis M t) ∧ f q = 0 := by
  have hsecond (e : Equiv.Perm (Fin 3))
      (hcross : f (M.position (M.orderedVertex t (e 0))) *
        f (M.position (M.orderedVertex t (e 2))) < 0) :=
    ordered_cut_geometry M f t ((Equiv.swap 1 2).trans e)
      (by simpa [Equiv.trans_apply, Equiv.swap_apply_def] using hcross)
  unfold localRefinementBoundaryCuts at hq
  split_ifs at hq with hp hn hep hen
  · let o := Classical.choice hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ordered_cut_geometry M f t o.perm
        (mul_neg_of_pos_of_neg o.positive o.negative_one)
    · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using
        hsecond o.perm (mul_neg_of_pos_of_neg o.positive o.negative_two)
  · let o := Classical.choice hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ordered_cut_geometry M f t o.perm
        (mul_neg_of_neg_of_pos o.negative o.positive_one)
    · simpa [Equiv.trans_apply, Equiv.swap_apply_def] using
        hsecond o.perm (mul_neg_of_neg_of_pos o.negative o.positive_two)
  · let o := Classical.choice hep
    simp only [List.mem_singleton] at hq
    subst q
    exact ordered_cut_geometry M f t o.perm (mul_neg_of_pos_of_neg o.positive o.negative)
  · let o := Classical.choice hen
    simp only [List.mem_singleton] at hq
    subst q
    exact ordered_cut_geometry M f t o.perm (mul_neg_of_neg_of_pos o.negative o.positive)
  · exact False.elim (List.not_mem_nil hq)

variable {S : Type*} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]



theorem meshTriangle_vertex_contribution_ordered_perm (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (t : M.Triangle) (e : Equiv.Perm (Fin 3)) (x : S) :
    let b := affineBasisOfTriangle (M.position ∘ M.orderedVertex t ∘ e)
      (M.orderedVertex_perm_affineIndependent t e)
    (∑ k : Fin 3, if F (b k) = x then coordinateTriangleAngle g F b k else 0) =
      ∑ k : Fin 3, if F (meshTriangleBasis M t k) = x then
        coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0 := by
  apply coordinateTriangle_vertex_contribution_eq_of_range_eq g F _ _ _ x
  rw [range_meshTriangleBasis]
  exact M.range_orderedVertex_perm t e




theorem localRefinementMesh_vertex_contribution (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (t : M.Triangle)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (ht : convexHull ℝ (range (meshTriangleBasis M t)) ⊆ F.source) (x : S) :
    meshVertexAngleContribution g F (M.localRefinementMesh f t) x =
      (∑ k : Fin 3, if F (meshTriangleBasis M t k) = x then
        coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0) +
      ((localRefinementBoundaryCuts M f t).map
        (fun q => if F q = x then Real.pi else 0)).sum := by
  have hsource (e : Equiv.Perm (Fin 3)) :
      convexHull ℝ (range (M.position ∘ M.orderedVertex t ∘ e)) ⊆ F.source := by
    rw [M.range_orderedVertex_perm, ← range_meshTriangleBasis]
    exact ht
  unfold TriangleMesh.localRefinementMesh localRefinementBoundaryCuts
  split_ifs with hp hn hep hen
  · let o := Classical.choice hp
    have h := strictMeshFor_vertex_contribution g F M f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) hF hFi (hsource o.perm)
      o.positive o.negative_one o.negative_two x
    dsimp only at h ⊢
    change meshVertexAngleContribution g F _ x = _ at h
    rw [h, meshTriangle_vertex_contribution_ordered_perm]
    simp only [o, Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, add_assoc]
  · let o := Classical.choice hn
    have h := strictNegativeMeshFor_vertex_contribution g F M f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) hF hFi (hsource o.perm)
      o.negative o.positive_one o.positive_two x
    dsimp only at h ⊢
    rw [h, meshTriangle_vertex_contribution_ordered_perm]
    simp only [o, Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, add_assoc]
  · let o := Classical.choice hep
    have h := edgeMeshFor_vertex_contribution g F M f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) hF hFi (hsource o.perm)
      o.positive o.negative x
    dsimp only at h ⊢
    change meshVertexAngleContribution g F _ x = _ at h
    rw [h, meshTriangle_vertex_contribution_ordered_perm]
    simp only [o, Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  · let o := Classical.choice hen
    have h := edgeNegativeMeshFor_vertex_contribution g F M f (M.orderedVertex t ∘ o.perm)
      (M.orderedVertex_perm_affineIndependent t o.perm) hF hFi (hsource o.perm)
      o.negative o.positive x
    dsimp only at h ⊢
    rw [h, meshTriangle_vertex_contribution_ordered_perm]
    simp only [o, Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
  · rw [unchangedMeshFor_vertex_contribution]
    simp only [List.map_nil, List.sum_nil, add_zero]
    rfl



theorem localRefinementMesh_vertex_contribution_finset (g : RiemannianMetric 2 S)
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
    (M : TriangleMesh) (f : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ) (t : M.Triangle)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (ht : convexHull ℝ (range (meshTriangleBasis M t)) ⊆ F.source) (x : S) :
    meshVertexAngleContribution g F (M.localRefinementMesh f t) x =
      (∑ k : Fin 3, if F (meshTriangleBasis M t k) = x then
        coordinateTriangleAngle g F (meshTriangleBasis M t) k else 0) +
      ∑ q ∈ (localRefinementBoundaryCuts M f t).toFinset,
        if F q = x then Real.pi else 0 := by
  rw [List.sum_toFinset _ (localRefinementBoundaryCuts_nodup M f t)]
  exact localRefinementMesh_vertex_contribution g F M f t hF hFi ht x

end PoincareConjecture.Topology.Surface

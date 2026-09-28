import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall

set_option autoImplicit false

open Set Metric Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

noncomputable def HamiltonProperDiskTriangulation.vertexBlock
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    SimplicialComplex ℝ E :=
  let : Fintype T.ambient.faces := T.finite.fintype
  T.ambient.barycentricDualBlock {(p : E)}

omit [FiniteDimensional ℝ E] in
private theorem dual_vertex_face_in_original_star
    (K : SimplicialComplex ℝ E) [Fintype K.faces] {p : E} (hp : p ∈ K.vertices)
    {s : Finset E} (hs : s ∈ (K.barycentricDualBlock {p}).faces) :
    ∃ t ∈ (K.closedStar p).faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  have hs' : s ∈ (K.barycentricSubdivision.closedStar p).faces := by
    rwa [← K.barycentricDualBlock_singleton_eq_closedStar hp]
  obtain ⟨a, ha, hchain, hsa, hpa⟩ :=
    (K.barycentricSubdivision_closedStar_faces hp s).mp hs'
  obtain ⟨m, hm, hmax⟩ := Finset.exists_maximal ha
  have him (i : K.faces) (hi : i ∈ a) : i.val ⊆ m.val := by
    rcases hchain i hi m hm with h | h
    · exact h
    · exact hmax hi h
  refine ⟨m.val, ⟨m.property, ?_⟩, ?_⟩
  · simpa only [Finset.insert_eq_of_mem (hpa m hm)] using m.property
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hsa ▸ hx)
    exact convexHull_mono (him i hi)
      (i.val.centroid_mem_convexHull (K.nonempty_of_mem_faces i.property))

omit [FiniteDimensional ℝ E] in

theorem HamiltonProperDiskTriangulation.vertexBlock_centered_chart
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices) :
    (T.vertexBlock p).faces.Finite ∧
      (p : E) ∈ (T.vertexBlock p).vertices ∧
      (T.vertexBlock p).closedStar p = T.vertexBlock p ∧
      (T.vertexBlock p).space ⊆ (T.pairChart p).chart.source ∧
      ∃ f : E → V, (T.vertexBlock p).AffineOnFaces f ∧
        InjOn f (T.vertexBlock p).space ∧ f p = 0 ∧
        (0 : V) ∈ interior (f '' (T.vertexBlock p).space) ∧
        ∀ x, f x = (T.pairChart p).chart x - (T.pairChart p).chart p := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  let H := (T.pairChart p).chart
  have hpK : (p : E) ∈ T.ambient.vertices := T.disk_le p.property
  have hNfinite : N.faces.Finite := T.ambient.barycentricDualBlock_finite {(p : E)}
  have hpN : (p : E) ∈ N.vertices := by
    simpa only [N, HamiltonProperDiskTriangulation.vertexBlock,
      Finset.centroid_singleton, id_eq] using
      T.ambient.faceCentroid_mem_barycentricDualBlock_vertices hpK
  have hNstar : N.closedStar p = N := by
    simpa only [N, HamiltonProperDiskTriangulation.vertexBlock,
      Finset.centroid_singleton, id_eq] using
      T.ambient.barycentricDualBlock_closedStar_faceCentroid hpK
  have hNsource : N.space ⊆ H.source := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨t, ht, hst⟩ := dual_vertex_face_in_original_star T.ambient hpK hs
    exact T.star_source p ((T.ambient.closedStar p).convexHull_subset_space ht (hst hxs))
  have hHaffine : N.AffineOnFaces H := by
    intro s hs
    obtain ⟨t, ht, hst⟩ := dual_vertex_face_in_original_star T.ambient hpK hs
    obtain ⟨a, ha⟩ := T.star_affine p t ht
    exact ⟨a, fun x hx => ha (hst hx)⟩
  have hpSource : (p : E) ∈ H.source := hNsource (N.vertices_subset_space hpN)
  have hpD : (p : E) ∈ D :=
    T.disk_space.subset (T.disk.vertices_subset_space p.property)
  have hpR : (p : E) ∈ R := by
    rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨hregion, hdisk⟩
    · exact interior_subset (hinside hpSource)
    · exact (hregion p hpSource).mpr ((hdisk p hpSource).mp hpD).1
  have hNint : (p : E) ∈ interior N.space := by
    let K' := T.ambient.barycentricSubdivision
    have hpK' : (p : E) ∈ K'.vertices :=
      (T.ambient.barycentricDualBlock_le {(p : E)}) hpN
    have hpint : (p : E) ∈ interior K'.space := by
      rw [show K'.space = T.ambient.space from
        T.ambient.barycentricSubdivision_isSubdivision.space_eq]
      exact T.region_interior hpR
    obtain ⟨ε, hε, hsub⟩ := K'.exists_ball_inter_space_subset_closedStar
      T.ambient.barycentricSubdivision_finite hpK'
    have hsmall : interior K'.space ∩ ball (p : E) ε ⊆ (K'.closedStar p).space :=
      fun _ hx => hsub ⟨interior_subset hx.1, hx.2⟩
    have h := interior_maximal hsmall (isOpen_interior.inter isOpen_ball)
      ⟨hpint, mem_ball_self hε⟩
    simpa only [N, HamiltonProperDiskTriangulation.vertexBlock,
      T.ambient.barycentricDualBlock_singleton_eq_closedStar hpK] using h
  let a : V →ᴬ[ℝ] V := ContinuousAffineMap.id ℝ V - ContinuousAffineMap.const ℝ V (H p)
  let f : E → V := fun x => H x - H p
  have hf : N.AffineOnFaces f := hHaffine.postcomp a
  have hinj : InjOn f N.space := by
    intro x hx y hy hxy
    exact H.injOn (hNsource hx) (hNsource hy) (sub_left_inj.mp hxy)
  have hfzero : f p = 0 := sub_self _
  have hHint : H p ∈ interior (H '' N.space) :=
    mem_interior_iff_mem_nhds.mpr (H.image_mem_nhds hpSource
      (mem_interior_iff_mem_nhds.mp hNint))
  let e := (ContinuousAffineEquiv.constVAdd ℝ V (-(H p))).toHomeomorph
  have hopen : IsOpen (e '' interior (H '' N.space)) := e.isOpenMap _ isOpen_interior
  have hsub : e '' interior (H '' N.space) ⊆ f '' N.space := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    refine ⟨x, hx, ?_⟩
    change H x - H p = -(H p) + H x
    rw [sub_eq_add_neg, add_comm]
  have hz : (0 : V) ∈ e '' interior (H '' N.space) := by
    refine ⟨H p, hHint, ?_⟩
    change -(H p) + H p = 0
    exact neg_add_cancel _
  exact ⟨hNfinite, hpN, hNstar, hNsource, f, hf, hinj, hfzero,
    interior_maximal hsub hopen hz, fun _ => rfl⟩

end PoincareConjecture.M76.HamiltonIndexOne

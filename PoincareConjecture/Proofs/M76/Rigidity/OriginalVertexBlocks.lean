import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskModelFacts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.DualVertexFaceContainment
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.OriginalDiskStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalProperDiskTriangulation

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  (T : OriginalProperDiskTriangulation e R j)

open Classical in


noncomputable def vertexBlock (p : (T.marked 2).vertices) :
    SimplicialComplex ℝ (T.index → ℝ × V3) :=
  let : Fintype T.ambient.faces := T.finite.fintype
  T.ambient.barycentricDualBlock {(p : T.index → ℝ × V3)}

open Classical in



theorem vertexBlock_centered_chart (p : (T.marked 2).vertices) :
    (T.vertexBlock p).faces.Finite ∧
      (p : T.index → ℝ × V3) ∈ (T.vertexBlock p).vertices ∧
      (T.vertexBlock p).closedStar p = T.vertexBlock p ∧
      MapsTo (fun x => (T.inverse x : X)) (T.vertexBlock p).space
        (T.chart (T.chart_index p)).source ∧
      ∃ f : (T.index → ℝ × V3) → C3,
        (T.vertexBlock p).AffineOnFaces f ∧
        InjOn f (T.vertexBlock p).space ∧ f p = 0 ∧
        (0 : C3) ∈ interior (f '' (T.vertexBlock p).space) ∧
        ∀ x, f x = T.chart (T.chart_index p) (T.inverse x) -
          T.chart (T.chart_index p) (T.inverse p) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  let N := T.vertexBlock p
  let H := T.chart (T.chart_index p)
  have hpK : (p : T.index → ℝ × V3) ∈ T.ambient.vertices := T.marked_le 2 p.property
  have hNfinite : N.faces.Finite := T.ambient.barycentricDualBlock_finite {p.val}
  have hpN : (p : T.index → ℝ × V3) ∈ N.vertices := by
    simpa only [N, vertexBlock, Finset.centroid_singleton, id_eq] using
      T.ambient.faceCentroid_mem_barycentricDualBlock_vertices hpK
  have hNstar : N.closedStar p = N := by
    simpa only [N, vertexBlock, Finset.centroid_singleton, id_eq] using
      T.ambient.barycentricDualBlock_closedStar_faceCentroid hpK
  have hNS : N.space ⊆ (T.ambient.closedStar p).space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨t, ht, hst⟩ :=
      T.ambient.exists_original_star_face_of_vertex_dual_face hpK hs
    exact (T.ambient.closedStar p).convexHull_subset_space ht (hst hxs)
  have hNsource : MapsTo (fun x => (T.inverse x : X)) N.space H.source :=
    fun _ hx => T.star_source p (hNS hx)
  have hHaffine : N.AffineOnFaces (fun x => H (T.inverse x)) := by
    intro s hs
    obtain ⟨t, ht, hst⟩ :=
      T.ambient.exists_original_star_face_of_vertex_dual_face hpK hs
    obtain ⟨a, ha⟩ := T.star_affine p t ht
    exact ⟨a, fun _ hx => ha (hst hx)⟩
  let K' := T.ambient.barycentricSubdivision
  have hKs : K'.space = T.ambient.space :=
    T.ambient.barycentricSubdivision_isSubdivision.space_eq
  let H' : T.neighborhood ≃ₜ K'.space :=
    T.model.trans (Homeomorph.setCongr hKs.symm)
  have hg' (z : K'.space) : (T.inverse z : X) = (H'.symm z : X) :=
    T.inverse_eq ⟨z, hKs.subset z.property⟩
  have hpK' : (p : T.index → ℝ × V3) ∈ K'.vertices :=
    (T.ambient.barycentricDualBlock_le {p.val}) hpN
  have hpD : (T.inverse p : X) ∈ j '' closedBall (0 : V2) 1 :=
    (T.inverse_mem_disk_iff (T.ambient.vertices_subset_space hpK)).mpr
      ((T.marked 2).vertices_subset_space p.property)
  have hpR : (T.inverse p : X) ∈ R := by
    obtain ⟨z, hz, hzp⟩ := hpD
    exact hzp ▸ T.disk_in_region hz
  have hNs : N = K'.closedStar p :=
    T.ambient.barycentricDualBlock_singleton_eq_closedStar hpK
  have hsource' : MapsTo (fun x => (T.inverse x : X)) (K'.closedStar p).space
      H.source := by
    rw [← hNs]
    exact hNsource
  obtain ⟨hHinj, _, hHint⟩ := K'.exists_original_open_neighborhood_inside_closedStar
    T.ambient.barycentricSubdivision_finite H' T.inverse hg' hpK'
    (T.region_interior hpR) H hsource'
  rw [← hNs] at hHinj hHint
  let a : C3 →ᴬ[ℝ] C3 := ContinuousAffineMap.id ℝ C3 -
    ContinuousAffineMap.const ℝ C3 (H (T.inverse p))
  let f : (T.index → ℝ × V3) → C3 :=
    fun x => H (T.inverse x) - H (T.inverse p)
  have hf : N.AffineOnFaces f := hHaffine.postcomp a
  have hfi : InjOn f N.space := by
    intro x hx y hy hxy
    exact hHinj hx hy (sub_left_inj.mp hxy)
  have hfp : f p = 0 := sub_self _
  let aH := (ContinuousAffineEquiv.constVAdd ℝ C3 (-(H (T.inverse p)))).toHomeomorph
  have hopen : IsOpen (aH '' interior ((fun x => H (T.inverse x)) '' N.space)) :=
    aH.isOpenMap _ isOpen_interior
  have hsub : aH '' interior ((fun x => H (T.inverse x)) '' N.space) ⊆
      f '' N.space := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := interior_subset hy
    refine ⟨x, hx, ?_⟩
    change H (T.inverse x) - H (T.inverse p) = -H (T.inverse p) + H (T.inverse x)
    rw [sub_eq_add_neg, add_comm]
  have hz : (0 : C3) ∈ aH '' interior ((fun x => H (T.inverse x)) '' N.space) := by
    refine ⟨H (T.inverse p), hHint, ?_⟩
    change -H (T.inverse p) + H (T.inverse p) = 0
    exact neg_add_cancel _
  exact ⟨hNfinite, hpN, hNstar, hNsource, f, hf, hfi, hfp,
    interior_maximal hsub hopen hz, fun _ => rfl⟩

end PoincareConjecture.M76.OriginalProperDiskTriangulation

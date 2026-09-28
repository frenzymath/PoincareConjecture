import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskVertexBlocks
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set Metric Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V" => ((ℝ × ℝ) × ℝ)
local notation "P2" => (ℝ × ℝ)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E] {R D : Set E} {b : closedBall (0 : V2) 1 ≃ₜ D}

theorem HamiltonProperDiskTriangulation.exists_frontier_star_plane_chart
    (T : HamiltonProperDiskTriangulation R D b) (p : T.disk.vertices)
    (hpfront : (p : E) ∈ frontier R) :
    ∃ f : E → P2, (T.boundary.closedStar p).AffineOnFaces f ∧
      InjOn f (T.boundary.closedStar p).space ∧
      f p ∈ interior (f '' (T.boundary.closedStar p).space) ∧
      ∀ x, f x = (((T.pairChart p).chart x).1.2, ((T.pairChart p).chart x).2) := by
  classical
  let H := (T.pairChart p).chart
  let S := T.boundary.closedStar p
  have hpK : (p : E) ∈ T.ambient.vertices := T.disk_le p.property
  have hpKface : {(p : E)} ∈ T.ambient.faces := hpK
  have hpH : (p : E) ∈ H.source := T.star_source p
    ((T.ambient.closedStar p).vertices_subset_space
      ⟨hpKface, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
        using hpKface⟩)
  have hhalf : ∀ x ∈ H.source, x ∈ R ↔ 0 ≤ (H x).1.1 := by
    rcases (T.pairChart p).model with ⟨hinside, _⟩ | ⟨hhalf, _⟩
    · exact False.elim (hpfront.2 (hinside hpH))
    · exact hhalf
  let ell : V →L[ℝ] ℝ :=
    { toFun := fun z => z.1.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  let rho : V →L[ℝ] P2 :=
    { toFun := fun z => (z.1.2, z.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := by fun_prop }
  let a : P2 →L[ℝ] V :=
    { toFun := fun z => ((0, z.1), z.2)
      map_add' := by intro x y; simp
      map_smul' := by intro c x; simp
      cont := by fun_prop }
  have hell : ell.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
    intro he
    have h := congrArg (fun m : V →ₗ[ℝ] ℝ => m ((1, 0), 0)) he
    change (1 : ℝ) = 0 at h
    exact one_ne_zero h
  have hfront := H.isImage_frontier_of_affine_nonneg ell.toContinuousAffineMap hell hhalf
  obtain ⟨q, hqs, _, hqval, _⟩ := H.exists_affine_hypersurface_chart
    ell.toContinuousAffineMap hfront a.toContinuousAffineMap rho.toContinuousAffineMap
    (fun z => rfl) (by
      intro z hz
      change ((0, z.1.2), z.2) = z
      apply Prod.ext
      · exact Prod.ext hz.symm rfl
      · rfl)
    (fun _ => rfl) ⟨p, hpfront⟩
  have hSS : S.space ⊆ H.source := by
    apply Subset.trans ?_ (T.star_source p)
    exact SimplicialComplex.space_subset_of_le
      (fun s hs => ⟨T.boundary_le hs.1, T.boundary_le hs.2⟩)
  have hSF : S.space ⊆ frontier R :=
    (SimplicialComplex.space_subset_of_le
      (show S ≤ T.boundary from fun s hs => hs.1)).trans T.boundary_space.subset
  let f : E → P2 := fun x => rho (H x)
  have hf : S.AffineOnFaces f :=
    (show S.AffineOnFaces H from fun s hs =>
      T.star_affine p s ⟨T.boundary_le hs.1, T.boundary_le hs.2⟩).postcomp
        rho.toContinuousAffineMap
  have hfi : InjOn f S.space := by
    intro x hx y hy hxy
    change ((H x).1.2, (H x).2) = ((H y).1.2, (H y).2) at hxy
    have hxzero := (hfront.apply_mem_iff (hSS hx)).mpr (hSF hx)
    have hyzero := (hfront.apply_mem_iff (hSS hy)).mpr (hSF hy)
    apply H.injOn (hSS hx) (hSS hy)
    apply Prod.ext
    · apply Prod.ext
      · exact hxzero.trans hyzero.symm
      · exact congrArg (fun z : P2 => z.1) hxy
    · exact congrArg (fun z : P2 => z.2) hxy
  have hpF : (p : E) ∈ T.boundary.vertices := by
    obtain ⟨s, hs, hps⟩ := SimplicialComplex.mem_space_iff.mp
      (T.boundary_space.symm.subset hpfront)
    have hpins := (T.ambient.vertex_mem_convexHull_iff hpK (T.boundary_le hs)).mp hps
    exact T.boundary.face_subset_vertices hs hpins
  obtain ⟨r, hr, hrS⟩ := T.boundary.exists_ball_inter_space_subset_closedStar
    (T.finite.subset T.boundary_le) hpF
  have hcont : ContinuousAt (Subtype.val : frontier R → E) ⟨p, hpfront⟩ :=
    continuous_subtype_val.continuousAt
  have hN : (Subtype.val ⁻¹' S.space : Set (frontier R)) ∈ 𝓝 ⟨p, hpfront⟩ := by
    apply Filter.mem_of_superset
      (hcont.preimage_mem_nhds (ball_mem_nhds (p : E) hr))
    intro x hx
    exact hrS ⟨T.boundary_space.symm.subset x.property, hx⟩
  have hpq : (⟨p, hpfront⟩ : frontier R) ∈ q.source := by
    rw [hqs]
    exact hpH
  have hqint : q ⟨p, hpfront⟩ ∈ interior (q '' (Subtype.val ⁻¹' S.space)) :=
    mem_interior_iff_mem_nhds.mpr (q.image_mem_nhds hpq hN)
  have himage : q '' (Subtype.val ⁻¹' S.space) ⊆ f '' S.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hqval x).symm⟩
  refine ⟨f, hf, hfi, ?_, fun _ => rfl⟩
  have hint := interior_mono himage hqint
  rwa [hqval ⟨p, hpfront⟩] at hint

variable [FiniteDimensional ℝ E]

theorem HamiltonProperDiskTriangulation.frontier_edge_triangle_count
    (T : HamiltonProperDiskTriangulation R D b) {s : Finset E}
    (hsD : s ∈ T.disk.faces) (hsF : s ∈ T.boundary.faces) (hscard : s.card = 2) :
    {t : Finset E | t ∈ T.boundary.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2 := by
  classical
  obtain ⟨p, hps⟩ := T.disk.nonempty_of_mem_faces hsD
  have hpD := T.disk.face_subset_vertices hsD hps
  have hpF := T.boundary.face_subset_vertices hsF hps
  have hpfront := T.boundary_space.subset (T.boundary.vertices_subset_space hpF)
  obtain ⟨f, hf, hi, hint, _⟩ := T.exists_frontier_star_plane_chart ⟨p, hpD⟩ hpfront
  let S := T.boundary.closedStar p
  have hsS : s ∈ S.faces := ⟨hsF, by simpa only [Finset.insert_eq_of_mem hps] using hsF⟩
  let J := hf.embeddedImage hi
  have hJ := hf.embeddedImage_finite hi (SimplicialComplex.finite_closedStar_faces
    (T.finite.subset T.boundary_le) p)
  have hsJ : s.image f ∈ J.faces := by
    rw [hf.embeddedImage_faces]
    exact ⟨s, hsS, rfl⟩
  have hscJ : (s.image f).card = Module.finrank ℝ P2 := by
    simpa [hscard] using Finset.card_image_iff.mpr (hi.mono (S.subset_space hsS))
  have hpint : f p ∈ interior J.space := by
    rw [hf.embeddedImage_space]
    exact hint
  have hcount := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hscJ
    ⟨f p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hpint⟩
  rw [hf.ncard_embeddedImage_faceLink hi hsS] at hcount
  have hlink : S.faceLink s = T.boundary.faceLink s := by
    simpa only [SimplicialComplex.closedFaceStar_singleton_eq_closedStar] using
      T.boundary.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rw [hlink, T.boundary.ncard_faceLink_vertices_eq_cofaces, hscard] at hcount
  exact hcount

end PoincareConjecture.M76.HamiltonIndexOne

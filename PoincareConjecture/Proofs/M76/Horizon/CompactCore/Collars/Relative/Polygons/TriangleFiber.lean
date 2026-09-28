import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.SurfaceIncidence
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.Nonboundary
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Polygons.TriangleNormalIntervals
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MaximalFaceDual
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PairedSignedFiber
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (-1 : ℝ) 1

theorem triangle_base_eq_singleton {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 3) :
    T.dualRegion s ∩ (T.marked 2).space = {s.centroid ℝ id} := by
  classical
  let : Fintype (T.marked 2).faces := (T.marked_finite 2).fintype
  rw [T.dualRegion_inter_surface]
  apply (T.marked 2).barycentricDualBlock_space_eq_singleton_of_maximal hs
  intro t ht hst
  exact (Finset.eq_of_subset_of_card_le hst (by
    rw [hcard]
    exact T.surface_face_card_le_three ht)).symm

theorem surface_triangle_not_boundary {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 3) :
    s ∉ (T.marked 1).faces := by
  intro hsB
  have hbound := T.rim_face_card_le_two ((T.surface_face_mem_boundary_iff hs).mp hsB)
  omega

theorem triangle_dualRegion_inter_boundary {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 3) :
    T.dualRegion s ∩ (T.marked 1).space = ∅ := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have h := T.nonboundary_dual_inter_boundary hs (T.surface_triangle_not_boundary hs hcard)
  exact eq_empty_iff_forall_notMem.mpr (fun _ hx => h.subset ⟨hx.1.1, hx.2⟩)

theorem exists_triangle_fiber {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hcard : s.card = 3) :
    ∃ F : ℝ → E, FinitePiecewiseAffineOn F I ∧ InjOn F I ∧
      F '' I = T.dualRegion s ∧ F 0 = s.centroid ℝ id ∧
      (∀ r ∈ I, F r ∈ T.dualRegionRim s ↔ r ∈ ({-1, 1} : Set ℝ)) ∧
      (∀ p : (T.marked 2).vertices, (p : E) ∈ s → ∀ r ∈ I,
        0 ≤ T.height p (F r) ↔ 0 ≤ r) ∧
      ∀ p : (T.marked 2).vertices, (p : E) ∈ s → ∀ r ∈ I,
        T.height p (F r) ≤ 0 ↔ r ≤ 0 := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  obtain ⟨p0, hp0⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let p : (T.marked 2).vertices := ⟨p0, (T.marked 2).face_subset_vertices hs hp0⟩
  have hps : (p : E) ∈ s := hp0
  let N := T.ambient.barycentricDualBlock s
  have hsB := T.surface_triangle_not_boundary hs hcard
  have hN : T.dualRegion s = N.space := T.dualRegion_eq_dualBlock_of_not_boundary hs hsB
  obtain ⟨t, ht, u, hu, hst, hsu, htc, huc, htu, _, hpair, _, hlink⟩ :=
    T.exists_triangle_normal_interval hs hcard
  have hQ : T.dualRegionRim s = {t.centroid ℝ id, u.centroid ℝ id} :=
    (T.dualRegionRim_eq_link_of_not_boundary hs hsB).trans hlink
  have hzero : T.dualRegion s ∩ {x | T.height p x = 0} = {s.centroid ℝ id} := by
    rw [← T.triangle_base_eq_singleton hs hcard]
    ext x
    exact and_congr_right (fun hx => T.height_eq_zero_iff_on_dualRegion p hps hx)
  let ell : C3 →ₗ[ℝ] ℝ := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hell : ell.toAffineMap.linear ≠ 0 := by
    intro he
    have hz := congrArg (fun m : C3 →ₗ[ℝ] ℝ => m ((0, 0), 1)) he
    norm_num [ell] at hz
  have hstar {v : Finset E} (hv : v ∈ T.ambient.faces)
      (hsv : s ⊆ v) : v ∈ (T.ambient.closedStar p).faces :=
    ⟨hv, by simpa only [Finset.insert_eq_of_mem (hsv hps)] using hv⟩
  have hvertexzero : ∀ x ∈ s, ell (T.chart p x) = 0 := by
    intro x hx
    change T.height p x = 0
    have hxS := (T.marked 2).subset_space hs hx
    exact (T.height_eq_zero_iff p
      ((T.ambient.closedStar p).subset_space (hstar (T.marked_le 2 hs) Subset.rfl) hx)
      (T.surface_subset_region hxS)).mpr hxS
  have hsign := (T.star_affine p).opposite_centroid_signs
    (T.star_injective p) (hstar (T.marked_le 2 hs) Subset.rfl)
    (hstar ht hst) (hstar hu hsu)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using hcard)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using htc)
    (by simpa only [Module.finrank_prod, Module.finrank_self] using huc)
    hst hsu htu ell.toAffineMap hell hvertexzero
  obtain ⟨F, hF, hi, him, h0, hrim, hpos, hneg⟩ :=
    PoincareConjecture.M76.exists_finitePL_fiber_of_paired_ends (hN.symm ▸ hpair) (T.height p)
      (T.continuousOn_height_dualRegion p hps) hzero hsign
  refine ⟨F, hF, hi, him, h0, ?_, ?_, ?_⟩
  · simpa only [hQ] using hrim
  · intro q hqs r hr
    have hx : F r ∈ T.dualRegion s := him.subset (mem_image_of_mem F hr)
    exact (T.nonneg_agree q p (F r)
      (T.dualRegion_subset_star q hqs hx) (T.dualRegion_subset_star p hps hx)).trans
      (hpos r hr)
  · intro q hqs r hr
    have hx : F r ∈ T.dualRegion s := him.subset (mem_image_of_mem F hr)
    exact (T.nonpos_agree q p
      (T.dualRegion_subset_star q hqs hx) (T.dualRegion_subset_star p hps hx)).trans
      (hneg r hr)

end Geometry.SimplicialComplex.CoorientedSurfaceStars

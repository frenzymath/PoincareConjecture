import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Model.SurfaceIncidence
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Regions.Nonboundary
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedStarEdgeLink
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolygonLinkDualDisk
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedStarCofaces
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CompleteCofaceDualBlock
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualContact

set_option autoImplicit false
open Set

namespace Geometry.SimplicialComplex.CoorientedSurfaceStars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] (T : CoorientedSurfaceStars E)

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

open Classical in
theorem isFinitePLBallPair_edge_dualBlock {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 2) :
    let : Fintype T.ambient.faces := T.finite.fintype
    IsFinitePLBallPair P2 (T.ambient.barycentricDualBlock s).space
      ((T.ambient.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  obtain ⟨p, hps⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let pS : (T.marked 2).vertices := ⟨p, (T.marked 2).face_subset_vertices hs hps⟩
  obtain ⟨n, P, hPi, hP, hPs⟩ := T.ambient.exists_polygon_faceLink_of_embedded_star
    T.finite (show Module.finrank ℝ C3 = 3 by simp)
    (T.marked_le 2 hs) hscard hps (T.chart pS)
    (T.star_affine pS) (T.star_injective pS) (T.star_interior pS)
  exact T.ambient.isFinitePLBallPair_dualBlock_of_polygon_faceLink
    (T.marked_le 2 hs) P hPi hP hPs

omit [FiniteDimensional ℝ E] in

theorem exists_boundary_star_plane_chart (p : (T.marked 2).vertices)
    (hpB : (p : E) ∈ (T.marked 1).space) :
    ∃ f : E → P2, ((T.marked 1).closedStar p).AffineOnFaces f ∧
      InjOn f ((T.marked 1).closedStar p).space ∧
      f p ∈ interior (f '' ((T.marked 1).closedStar p).space) ∧
      ∀ x, f x = ((T.chart p x).1.2, (T.chart p x).2) := by
  have hmodel := T.boundary_chart_model p hpB
  have hp : (p : E) ∈ (T.marked 1).vertices := by
    apply T.ambient.face_mem_subcomplex_of_intrinsicInterior (T.marked 1)
      (T.marked_le 1) (T.marked_le 2 p.property) (x := (p : E))
    · simp
    · exact hpB
  let pi : C3 →L[ℝ] P2 :=
    { toFun := fun z ↦ (z.1.2, z.2)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := by fun_prop }
  let f : E → P2 := pi ∘ T.chart p
  let j : P2 → C3 := fun z ↦ ((0, z.1), z.2)
  have hj : Continuous j := by fun_prop
  have hstar := T.ambient.closedStar_space_eq_inter_of_full (T.marked 1)
    T.finite (T.marked_le 1) (T.marked_full 1) hp
  have hle : (T.marked 1).closedStar p ≤ T.ambient.closedStar p :=
    fun _ hs ↦ ⟨T.marked_le 1 hs.1, T.marked_le 1 hs.2⟩
  have hplane {x : E} (hx : x ∈ ((T.marked 1).closedStar p).space) :
      j (f x) = T.chart p x := by
    have hx' := hstar.subset hx
    have hz := (hmodel.2 x hx'.1).mp hx'.2
    exact Prod.ext (Prod.ext hz.symm rfl) rfl
  have hpstar : (p : E) ∈ ((T.marked 1).closedStar p).space := by
    apply ((T.marked 1).closedStar p).vertices_subset_space
    have hpface : {(p : E)} ∈ (T.marked 1).faces := hp
    exact ⟨hpface, by simpa using hpface⟩
  refine ⟨f, (show ((T.marked 1).closedStar p).AffineOnFaces (T.chart p) from
    fun _ hs ↦ T.star_affine p _ (hle hs)).postcomp pi.toContinuousAffineMap, ?_, ?_,
      fun _ ↦ rfl⟩
  · intro x hx y hy hxy
    exact T.star_injective p (hstar.subset hx).1 (hstar.subset hy).1
      ((hplane hx).symm.trans ((congrArg j hxy).trans (hplane hy)))
  · have hsub : j ⁻¹' interior (T.chart p '' (T.ambient.closedStar p).space) ⊆
        f '' ((T.marked 1).closedStar p).space := by
      intro z hz
      obtain ⟨x, hx, hfx⟩ := interior_subset hz
      have hxB : x ∈ (T.marked 1).space := (hmodel.2 x hx).mpr (by rw [hfx])
      refine ⟨x, hstar.symm.subset ⟨hx, hxB⟩, ?_⟩
      change pi (T.chart p x) = z
      rw [hfx]
      exact Prod.ext rfl rfl
    apply interior_maximal hsub (isOpen_interior.preimage hj)
    change j (f p) ∈ interior (T.chart p '' (T.ambient.closedStar p).space)
    rw [hplane hpstar]
    exact T.star_interior p

open Classical in
theorem exists_boundary_edge_dual_interval {s : Finset E}
    (hs : s ∈ (T.marked 2).faces) (hsB : s ∈ (T.marked 1).faces)
    (hscard : s.card = 2) :
    let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
    ∃ t ∈ (T.marked 1).faces, ∃ v ∈ (T.marked 1).faces,
      s ⊆ t ∧ s ⊆ v ∧ t.card = 3 ∧ v.card = 3 ∧ t ≠ v ∧
      IsFinitePLBallPair ℝ ((T.marked 1).barycentricDualBlock s).space
        {t.centroid ℝ id, v.centroid ℝ id} ∧
      (((T.marked 1).barycentricDualBlock s).link (s.centroid ℝ id)).space =
        {t.centroid ℝ id, v.centroid ℝ id} := by
  classical
  let : Fintype (T.marked 1).faces := (T.marked_finite 1).fintype
  obtain ⟨p, hps⟩ := (T.marked 2).nonempty_of_mem_faces hs
  let pS : (T.marked 2).vertices := ⟨p, (T.marked 2).face_subset_vertices hs hps⟩
  obtain ⟨f, hf, hi, hint, _⟩ :=
    T.exists_boundary_star_plane_chart pS ((T.marked 1).subset_space hsB hps)
  have hcard : s.card = Module.finrank ℝ P2 := by simpa using hscard
  obtain ⟨t, ht, v, hv, hst, hsv, htc, hvc, htv, hexhaust⟩ :=
    (T.marked 1).exists_paired_facet_of_embedded_star (T.marked_finite 1)
      hsB hcard hps f hf hi hint
  have htc' : t.card = 3 := by simpa using htc
  have hvc' : v.card = 3 := by simpa using hvc
  let S := (T.marked 1).closedStar p
  let : Fintype S.faces := (finite_closedStar_faces (T.marked_finite 1) p).fintype
  have hbound : ∀ u ∈ S.faces, u.card ≤ 2 + 1 := by
    intro u hu
    simpa using hf.face_card_le_of_injOn hi hu
  have hcoface {u : Finset E} (hu : u ∈ (T.marked 1).faces) (hsu : s ⊆ u) :
      u ∈ S.faces := ⟨hu, by simpa only [Finset.insert_eq_of_mem (hsu hps)] using hu⟩
  have hdual : S.barycentricDualBlock s = (T.marked 1).barycentricDualBlock s :=
    (T.marked 1).barycentricDualBlock_eq_of_cofaces_in_subcomplex S
      (fun _ hu ↦ hu.1) s (fun _ hu hsu ↦ hcoface hu hsu)
  have hpair := S.isFinitePLBallPair_barycentricDualBlock_of_paired_facet hbound
    (hcoface hsB Subset.rfl) (hcoface ht hst) (hcoface hv hsv)
    hscard htc' hvc' hst hsv htv (fun u hu hsu huc ↦ hexhaust u hu.1 hsu (by simpa using huc))
  have hlink := S.barycentricDualBlock_link_space_of_paired_facet hbound
    (hcoface hsB Subset.rfl) (hcoface ht hst) (hcoface hv hsv)
    hscard htc' hvc' hst hsv (fun u hu hsu huc ↦ hexhaust u hu.1 hsu (by simpa using huc))
  rw [hdual] at hpair hlink
  exact ⟨t, ht, v, hv, hst, hsv, htc', hvc', htv, hpair.1, hlink⟩

open Classical in
theorem exists_edge_chart_sign_witnesses
    (p : (T.marked 2).vertices) {s t : Finset E} (hps : (p : E) ∈ s)
    (hs : s ∈ (T.marked 2).faces) (hscard : s.card = 2)
    (ht : t ∈ T.ambient.faces) (htcard : t.card = 3) (hst : s ⊆ t)
    (A : C3 →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hzero : ∀ x ∈ t, A (T.chart p x) = 0) :
    let : Fintype T.ambient.faces := T.finite.fintype
    ∃ u ∈ T.ambient.faces, ∃ v ∈ T.ambient.faces,
      t ⊆ u ∧ t ⊆ v ∧ u.card = 4 ∧ v.card = 4 ∧
      u.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space ∧
      v.centroid ℝ id ∈ ((T.ambient.barycentricDualBlock s).link
        (s.centroid ℝ id)).space ∧
      A (T.chart p (u.centroid ℝ id)) < 0 ∧ 0 < A (T.chart p (v.centroid ℝ id)) := by
  classical
  let : Fintype T.ambient.faces := T.finite.fintype
  have h3 : Module.finrank ℝ C3 = 3 := by simp
  obtain ⟨u, hu, v, hv, htu, htv, huc, hvc, huv, _⟩ :=
    T.ambient.exists_paired_facet_of_embedded_star T.finite ht
      (htcard.trans h3.symm) (hst hps) (T.chart p)
      (T.star_affine p) (T.star_injective p) (T.star_interior p)
  have huc' : u.card = 4 := by simpa only [h3] using huc
  have hvc' : v.card = 4 := by simpa only [h3] using hvc
  have hstar {w : Finset E} (hw : w ∈ T.ambient.faces) (htw : t ⊆ w) :
      w ∈ (T.ambient.closedStar p).faces :=
    ⟨hw, by simpa only [Finset.insert_eq_of_mem (htw (hst hps))] using hw⟩
  have hsign := (T.star_affine p).opposite_centroid_signs (T.star_injective p)
    (hstar ht Subset.rfl) (hstar hu htu) (hstar hv htv)
    (htcard.trans h3.symm) huc hvc htu htv huv A hA hzero
  have hmark {w : Finset E} (hw : w ∈ T.ambient.faces) (htw : t ⊆ w)
      (hwc : w.card = 4) : w.centroid ℝ id ∈
      ((T.ambient.barycentricDualBlock s).link (s.centroid ℝ id)).space := by
    apply T.ambient.cofaceCentroid_mem_dualBlock_link (T.marked_le 2 hs) hw (hst.trans htw)
    intro he
    rw [he, hwc] at hscard
    omega
  rcases hsign with h | h
  · exact ⟨u, hu, v, hv, htu, htv, huc', hvc', hmark hu htu huc',
      hmark hv htv hvc', h.1, h.2⟩
  · exact ⟨v, hv, u, hu, htv, htu, hvc', huc', hmark hv htv hvc',
      hmark hu htu huc', h.2, h.1⟩

end Geometry.SimplicialComplex.CoorientedSurfaceStars

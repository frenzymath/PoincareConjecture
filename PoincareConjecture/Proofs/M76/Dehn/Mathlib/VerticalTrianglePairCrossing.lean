import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VerticalTriangleGerm
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoRayCrossingCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms
import Mathlib.Topology.OpenPartialHomeomorph.Basic










set_option autoImplicit false

open Set Geometry

namespace Geometry




theorem distinct_rays_of_vertical_triangle_intersection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (c d : ℝ)
    (hinter : ∀ x : E × ℝ,
      x ∈ convexHull ℝ ({(0, a), (0, b), (u, c)} : Set (E × ℝ)) →
      x ∈ convexHull ℝ ({(0, a), (0, b), (v, d)} : Set (E × ℝ)) → x.1 = 0) :
    ∀ t : ℝ, 0 < t → u ≠ t • v := by
  obtain ⟨U, hU, hzeroU, htriU⟩ := exists_open_vertical_triangle_germ hu ha hb c
  obtain ⟨V, hV, hzeroV, htriV⟩ := exists_open_vertical_triangle_germ hv ha hb d
  intro t ht heq
  obtain ⟨r, hr, hrUV⟩ := Set.exists_pos_smul_mem_of_mem_nhds
    ((hU.inter hV).mem_nhds ⟨hzeroU, hzeroV⟩) ((u, 0) : E × ℝ)
  have hfirst := (htriU _ hrUV.1).mpr ⟨r, hr.1.le, rfl⟩
  have hsecond := (htriV _ hrUV.2).mpr
    ⟨r * t, mul_nonneg hr.1.le ht.le, by
      change r • u = (r * t) • v
      rw [heq, mul_smul]⟩
  exact smul_ne_zero hr.1.ne' hu (hinter _ hfirst hsecond)

local notation "V2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)





theorem exists_vertical_triangle_pair_crossing_chart
    {u v : V2} (hu : u ≠ 0) (hv : v ≠ 0) {a b : ℝ}
    (ha : a < 0) (hb : 0 < b) (c d : ℝ)
    (hinter : ∀ x : C3,
      x ∈ convexHull ℝ ({(0, a), (0, b), (u, c)} : Set C3) →
      x ∈ convexHull ℝ ({(0, a), (0, b), (v, d)} : Set C3) → x.1 = 0)
    {O : Set C3} (hO : IsOpen O) (hzeroO : (0 : C3) ∈ O) :
    ∃ H : OpenPartialHomeomorph C3 C3,
      (0 : C3) ∈ H.source ∧ H.source ⊆ O ∧ H 0 = 0 ∧
      H ∈ piecewiseAffineGroupoid C3 ∧
      (∀ x ∈ H.source, (H x).2 = x.2) ∧
      ∀ x ∈ H.source,
        (x ∈ convexHull ℝ ({(0, a), (0, b), (u, c)} : Set C3) ∪
          convexHull ℝ ({(0, a), (0, b), (v, d)} : Set C3)) ↔ (H x).1.1 = 0 := by
  have hrays := distinct_rays_of_vertical_triangle_intersection hu hv ha hb c d hinter
  obtain ⟨F, hFPL, hFzero, hFlast, hFwhole⟩ :=
    ContinuousLinearMap.exists_standard_two_ray_crossing_coordinates hu hv hrays
  obtain ⟨V, hV, hzeroV, htriV⟩ := exists_open_vertical_triangle_germ hu ha hb c
  obtain ⟨W, hW, hzeroW, htriW⟩ := exists_open_vertical_triangle_germ hv ha hb d
  let U := O ∩ (V ∩ W)
  have hU : IsOpen U := hO.inter (hV.inter hW)
  let H := F.toOpenPartialHomeomorphOfImageEq U hU (F '' U) rfl
  have hsource : H.source = U := rfl
  have hforward (x : C3) : H x = F x := rfl
  have hF : LocallyPiecewiseAffineOn F univ ∧
      LocallyPiecewiseAffineOn F.symm univ := hFPL
  refine ⟨H, ⟨hzeroO, hzeroV, hzeroW⟩, fun _ hx => hx.1, hFzero, ?_,
    fun x _ => hFlast x, ?_⟩
  · exact ⟨hF.1.mono H.open_source (subset_univ _),
      hF.2.mono H.open_target (subset_univ _)⟩
  · intro x hx
    have hxU := hsource.subset hx
    rw [hforward]
    exact (or_congr (htriV x hxU.2.1) (htriW x hxU.2.2)).trans (hFwhole x)

end Geometry

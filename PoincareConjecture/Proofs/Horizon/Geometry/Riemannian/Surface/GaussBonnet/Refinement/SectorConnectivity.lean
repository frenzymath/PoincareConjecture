import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.SectorComplements
import Mathlib.Analysis.Convex.PathConnected

set_option autoImplicit false

open Set Filter
open scoped Topology
open Poincare.Topology.Plane.Meshes

namespace PoincareConjecture.Topology.Surface

noncomputable section

def coordinateBox (c : AffineBasis (Fin 3) ℝ Plane) (r : ℝ) : Set Plane :=
  {z | -r < c.coord 1 z ∧ c.coord 1 z < r} ∩
    {z | -r < c.coord 2 z ∧ c.coord 2 z < r}

theorem isOpen_coordinateBox (c : AffineBasis (Fin 3) ℝ Plane) (r : ℝ) :
    IsOpen (coordinateBox c r) :=
  (isOpen_Ioo.preimage (continuous_barycentric_coord c 1)).inter
    (isOpen_Ioo.preimage (continuous_barycentric_coord c 2))

theorem vertex_mem_coordinateBox (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ} (hr : 0 < r) :
    c 0 ∈ coordinateBox c r := by
  simpa [coordinateBox] using And.intro (And.intro hr hr) (And.intro hr hr)

theorem coordinateBox_mem_nhds (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ} (hr : 0 < r) :
    coordinateBox c r ∈ 𝓝 (c 0) :=
  (isOpen_coordinateBox c r).mem_nhds (vertex_mem_coordinateBox c hr)

theorem convex_coordinateBox (c : AffineBasis (Fin 3) ℝ Plane) (r : ℝ) :
    Convex ℝ (coordinateBox c r) :=
  ((convex_Ioo (-r) r).affine_preimage (c.coord 1)).inter
    ((convex_Ioo (-r) r).affine_preimage (c.coord 2))

private def diagonalPoint (c : AffineBasis (Fin 3) ℝ Plane) (t : ℝ) : Plane :=
  AffineMap.lineMap (c 0) (AffineMap.lineMap (c 1) (c 2) (1 / 2 : ℝ)) t

private theorem diagonalPoint_coords (c : AffineBasis (Fin 3) ℝ Plane) (t : ℝ) :
    c.coord 1 (diagonalPoint c t) = t / 2 ∧ c.coord 2 (diagonalPoint c t) = t / 2 := by
  simp [diagonalPoint, AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, mul_comm]
  constructor <;> ring

theorem coordinateBox_positive_nonempty (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ}
    (hr : 0 < r) :
    (coordinateBox c r ∩ {z | 0 < c.coord 1 z ∧ 0 < c.coord 2 z}).Nonempty := by
  refine ⟨diagonalPoint c r, ?_⟩
  have h := diagonalPoint_coords c r
  change ((-r < _ ∧ _ < r) ∧ (-r < _ ∧ _ < r)) ∧ 0 < _ ∧ 0 < _
  rw [h.1, h.2]
  exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
    by linarith, by linarith⟩

theorem coordinateBox_positive_isPreconnected (c : AffineBasis (Fin 3) ℝ Plane) (r : ℝ) :
    IsPreconnected (coordinateBox c r ∩ {z | 0 < c.coord 1 z ∧ 0 < c.coord 2 z}) :=
  ((convex_coordinateBox c r).inter
    (((convex_Ioi (0 : ℝ)).affine_preimage (c.coord 1)).inter
      ((convex_Ioi (0 : ℝ)).affine_preimage (c.coord 2)))).isPreconnected

theorem coordinateBox_positive_isConnected (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ}
    (hr : 0 < r) :
    IsConnected (coordinateBox c r ∩ {z | 0 < c.coord 1 z ∧ 0 < c.coord 2 z}) :=
  ⟨coordinateBox_positive_nonempty c hr, coordinateBox_positive_isPreconnected c r⟩

private theorem diagonalPoint_negative_mem (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ}
    (hr : 0 < r) :
    diagonalPoint c (-r) ∈ coordinateBox c r ∧
      c.coord 1 (diagonalPoint c (-r)) < 0 ∧ c.coord 2 (diagonalPoint c (-r)) < 0 := by
  have h := diagonalPoint_coords c (-r)
  change ((-r < _ ∧ _ < r) ∧ (-r < _ ∧ _ < r)) ∧ _ < 0 ∧ _ < 0
  rw [h.1, h.2]
  exact ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩,
    by linarith, by linarith⟩

theorem coordinateBox_reflex_nonempty (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ}
    (hr : 0 < r) :
    (coordinateBox c r ∩ {z | c.coord 1 z < 0 ∨ c.coord 2 z < 0}).Nonempty := by
  have h := diagonalPoint_negative_mem c hr
  exact ⟨diagonalPoint c (-r), h.1, Or.inl h.2.1⟩

theorem coordinateBox_reflex_isPreconnected (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ}
    (hr : 0 < r) :
    IsPreconnected (coordinateBox c r ∩ {z | c.coord 1 z < 0 ∨ c.coord 2 z < 0}) := by
  change IsPreconnected (coordinateBox c r ∩
    ({z | c.coord 1 z < 0} ∪ {z | c.coord 2 z < 0}))
  rw [inter_union_distrib_left]
  have h := diagonalPoint_negative_mem c hr
  exact ((convex_coordinateBox c r).inter
    ((convex_Iio (0 : ℝ)).affine_preimage (c.coord 1))).isPreconnected.union
      (diagonalPoint c (-r)) ⟨h.1, h.2.1⟩ ⟨h.1, h.2.2⟩
      ((convex_coordinateBox c r).inter
        ((convex_Iio (0 : ℝ)).affine_preimage (c.coord 2))).isPreconnected

theorem coordinateBox_reflex_isConnected (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ}
    (hr : 0 < r) :
    IsConnected (coordinateBox c r ∩ {z | c.coord 1 z < 0 ∨ c.coord 2 z < 0}) :=
  ⟨coordinateBox_reflex_nonempty c hr, coordinateBox_reflex_isPreconnected c hr⟩

theorem coordinateBox_positiveHalfspace_nonempty (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ}
    (hr : 0 < r) :
    (coordinateBox c r ∩ {z | 0 < c.coord 1 z}).Nonempty := by
  obtain ⟨z, hz, h1, _⟩ := coordinateBox_positive_nonempty c hr
  exact ⟨z, hz, h1⟩

theorem coordinateBox_positiveHalfspace_isPreconnected
    (c : AffineBasis (Fin 3) ℝ Plane) (r : ℝ) :
    IsPreconnected (coordinateBox c r ∩ {z | 0 < c.coord 1 z}) :=
  ((convex_coordinateBox c r).inter
    ((convex_Ioi (0 : ℝ)).affine_preimage (c.coord 1))).isPreconnected

theorem coordinateBox_negativeHalfspace_nonempty (c : AffineBasis (Fin 3) ℝ Plane) {r : ℝ}
    (hr : 0 < r) :
    (coordinateBox c r ∩ {z | c.coord 1 z < 0}).Nonempty := by
  have h := diagonalPoint_negative_mem c hr
  exact ⟨diagonalPoint c (-r), h.1, h.2.1⟩

theorem coordinateBox_negativeHalfspace_isPreconnected
    (c : AffineBasis (Fin 3) ℝ Plane) (r : ℝ) :
    IsPreconnected (coordinateBox c r ∩ {z | c.coord 1 z < 0}) :=
  ((convex_coordinateBox c r).inter
    ((convex_Iio (0 : ℝ)).affine_preimage (c.coord 1))).isPreconnected

theorem affineBasis_coordinate_reconstruction (c : AffineBasis (Fin 3) ℝ Plane) (z : Plane) :
    c 0 + c.coord 1 z • (c 1 - c 0) + c.coord 2 z • (c 2 - c 0) = z := by
  have hc := c.linear_combination_coord_eq_self z
  have hs := c.sum_coord_apply_eq_one z
  simp only [Fin.sum_univ_three] at hc hs
  have h0 : c.coord 0 z = 1 - c.coord 1 z - c.coord 2 z := by linarith
  rw [h0] at hc
  conv_rhs => rw [← hc]
  module

theorem exists_pos_coordinate_box_subset (c : AffineBasis (Fin 3) ℝ Plane)
    {U : Set Plane} (hU : U ∈ 𝓝 (c 0)) :
    ∃ r : ℝ, 0 < r ∧ coordinateBox c r ⊆ U := by
  let F : ℝ × ℝ → Plane := fun t => c 0 + t.1 • (c 1 - c 0) + t.2 • (c 2 - c 0)
  have hF : Continuous F := by fun_prop
  have hpre : F ⁻¹' U ∈ 𝓝 (0 : ℝ × ℝ) := by
    apply hF.continuousAt.preimage_mem_nhds
    simpa [F] using hU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r, hr, ?_⟩
  intro z hz
  have hp : (c.coord 1 z, c.coord 2 z) ∈ Metric.ball (0 : ℝ × ℝ) r := by
    rw [← ball_prod_same]
    exact ⟨by simpa [Real.dist_eq, abs_lt] using hz.1,
      by simpa [Real.dist_eq, abs_lt] using hz.2⟩
  have h := hball hp
  change c 0 + c.coord 1 z • (c 1 - c 0) + c.coord 2 z • (c 2 - c 0) ∈ U at h
  rwa [affineBasis_coordinate_reconstruction] at h

theorem closure_positiveSector (c : AffineBasis (Fin 3) ℝ Plane) :
    closure {z | 0 < c.coord 1 z ∧ 0 < c.coord 2 z} =
      {z | 0 ≤ c.coord 1 z ∧ 0 ≤ c.coord 2 z} := by
  rw [← interior_convexSector, closure_interior_convexSector]

private theorem firstCoordinate_surjective (c : AffineBasis (Fin 3) ℝ Plane) :
    Function.Surjective (c.coord 1) := by
  intro r
  exact ⟨AffineMap.lineMap (c 0) (c 1) r, by
    simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]⟩

theorem closure_positiveHalfspace (c : AffineBasis (Fin 3) ℝ Plane) :
    closure {z | 0 < c.coord 1 z} = {z | 0 ≤ c.coord 1 z} := by
  change closure (c.coord 1 ⁻¹' Ioi (0 : ℝ)) = c.coord 1 ⁻¹' Ici (0 : ℝ)
  rw [← ((c.coord 1).isOpenMap (continuous_barycentric_coord c 1)
    (firstCoordinate_surjective c)).preimage_closure_eq_closure_preimage
      (continuous_barycentric_coord c 1), closure_Ioi]

theorem closure_negativeHalfspace (c : AffineBasis (Fin 3) ℝ Plane) :
    closure {z | c.coord 1 z < 0} = {z | c.coord 1 z ≤ 0} := by
  change closure (c.coord 1 ⁻¹' Iio (0 : ℝ)) = c.coord 1 ⁻¹' Iic (0 : ℝ)
  rw [← ((c.coord 1).isOpenMap (continuous_barycentric_coord c 1)
    (firstCoordinate_surjective c)).preimage_closure_eq_closure_preimage
      (continuous_barycentric_coord c 1), closure_Iio]

theorem closure_openReflexSector (c : AffineBasis (Fin 3) ℝ Plane) :
    closure {z | c.coord 1 z < 0 ∨ c.coord 2 z < 0} =
      {z | c.coord 1 z ≤ 0 ∨ c.coord 2 z ≤ 0} := by
  have hs (i : Fin 3) (hi : i ≠ 0) : Function.Surjective (c.coord i) := by
    intro r
    exact ⟨AffineMap.lineMap (c 0) (c i) r, by
      simp [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring, hi]⟩
  have hcl (i : Fin 3) (hi : i ≠ 0) :
      closure {z | c.coord i z < 0} = {z | c.coord i z ≤ 0} := by
    change closure (c.coord i ⁻¹' Iio (0 : ℝ)) = c.coord i ⁻¹' Iic (0 : ℝ)
    rw [← ((c.coord i).isOpenMap (continuous_barycentric_coord c i) (hs i hi)).preimage_closure_eq_closure_preimage
      (continuous_barycentric_coord c i), closure_Iio]
  change closure ({z | c.coord 1 z < 0} ∪ {z | c.coord 2 z < 0}) = _
  rw [closure_union, hcl 1 (by decide), hcl 2 (by decide)]
  rfl

end

end PoincareConjecture.Topology.Surface

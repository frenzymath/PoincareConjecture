import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Boundary.BootstrapHalfBall

/-!
# Actual closed boundary data under the normal source isometry

The complex trace and its true within normal derivative are transported
to the coordinate-zero half-ball. C2 on that half-ball is then transported
back to the original complex map by the same linear equivalence.
Source: MT Lemma 19.31, pp. 464-466, finite boundary-bootstrap derivation,
Sections 2 and 7.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex
open scoped ContDiff Topology

namespace PoincareMT.M64.RampTransport

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin (n + 1))

private theorem boundaryComplexCoordinates_face (p : Plane) (hp : p 0 = 0) :
    boundaryComplexCoordinates p = (p 1 : ℂ) := by
  simp [boundaryComplexCoordinates, LinearIsometryEquiv.trans_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply, m64BoundaryCoordinateSwap_apply, hp]

/-- The actual complex closed C1 map and its mixed trace become the normal-coordinate-zero
data on the same radius half-ball. Source: MT Lemma 19.31 finite boundary bootstrap,
derivation Sections 2 and 7. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466; project
derivation `proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem boundaryComplexCoordinates_mixed_data
    {R : ℝ} (hR : 0 < R) {u : ℂ → Target}
    (hc : ContDiffOn ℝ 1 u (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}))
    (hs : ContDiffOn ℝ ∞ u (ball (0 : ℂ) R ∩ {z | 0 < z.im}))
    (ht : ∀ s : ℝ, |s| ≤ R → ∀ j : Fin (n + 1), j ≠ 0 → u (s : ℂ) j = 0)
    (hn : ∀ s : ℝ, |s| ≤ R →
      (fderivWithin ℝ u (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) (s : ℂ) I) 0 = 0) :
    ContDiffOn ℝ 1 (u ∘ boundaryComplexCoordinates) (boundaryClosedHalfBall R) ∧
      ContDiffOn ℝ ∞ (u ∘ boundaryComplexCoordinates) (boundaryHalfBall R) ∧
      (∀ j : Fin (n + 1), j ≠ 0 → ∀ p ∈ boundaryClosedHalfBall R,
        p 0 = 0 → (u ∘ boundaryComplexCoordinates) p j = 0) ∧
      ∀ p ∈ boundaryClosedHalfBall R, p 0 = 0 →
        (fderivWithin ℝ (u ∘ boundaryComplexCoordinates) (boundaryClosedHalfBall R) p
          (EuclideanSpace.single 0 1)) 0 = 0 := by
  let e := boundaryComplexCoordinates.toContinuousLinearEquiv
  have hpc : ContDiffOn ℝ 1 (u ∘ boundaryComplexCoordinates) (boundaryClosedHalfBall R) := by
    rw [← boundaryComplexCoordinates_preimage_closed]
    exact e.contDiffOn_comp_iff.mpr hc
  have hps : ContDiffOn ℝ ∞ (u ∘ boundaryComplexCoordinates) (boundaryHalfBall R) := by
    rw [← boundaryComplexCoordinates_preimage_open]
    exact e.contDiffOn_comp_iff.mpr hs
  have hfacebound (p : Plane) (hp : p ∈ boundaryClosedHalfBall R) (h0 : p 0 = 0) :
      |p 1| ≤ R := by
    have hh : ‖boundaryComplexCoordinates p‖ ≤ R := by
      rw [boundaryComplexCoordinates.norm_map]
      exact mem_closedBall_zero_iff.mp hp.1
    simpa only [boundaryComplexCoordinates_face p h0, norm_real, Real.norm_eq_abs] using hh
  refine ⟨hpc, hps, ?_, ?_⟩
  · intro j hj p hp h0
    simpa only [Function.comp_apply, boundaryComplexCoordinates_face p h0] using
      ht (p 1) (hfacebound p hp h0) j hj
  · intro p hp h0
    have hd : fderivWithin ℝ (u ∘ boundaryComplexCoordinates) (boundaryClosedHalfBall R) p =
        (fderivWithin ℝ u (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im})
          (boundaryComplexCoordinates p)).comp e.toContinuousLinearMap := by
      rw [← boundaryComplexCoordinates_preimage_closed]
      exact e.comp_right_fderivWithin (by
        change UniqueDiffWithinAt ℝ
          (boundaryComplexCoordinates ⁻¹' (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im})) p
        rw [boundaryComplexCoordinates_preimage_closed]
        exact (boundaryHalfBall_geometry hR).2.2.2.1 p hp)
    rw [hd]
    change (fderivWithin ℝ u (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im})
      (boundaryComplexCoordinates p) (boundaryComplexCoordinates (EuclideanSpace.single 0 1))) 0 = 0
    rw [boundaryComplexCoordinates_basis, if_pos rfl, boundaryComplexCoordinates_face p h0]
    exact hn (p 1) (hfacebound p hp h0)

/-- Closed C2 of the normalized source is exactly closed C2 of the same complex map. Source:
MT Lemma 19.31 finite boundary bootstrap, Section 7. Source: Morgan--Tian Lemma 19.31,
printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem contDiffOn_closedHalfDisk_of_boundaryComplexCoordinates
    {R : ℝ} {u : ℂ → Target}
    (hu : ContDiffOn ℝ 2 (u ∘ boundaryComplexCoordinates) (boundaryClosedHalfBall R)) :
    ContDiffOn ℝ 2 u (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) := by
  rw [← boundaryComplexCoordinates_preimage_closed] at hu
  exact boundaryComplexCoordinates.toContinuousLinearEquiv.contDiffOn_comp_iff.mp hu

end PoincareMT.M64.RampTransport

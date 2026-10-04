import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Boundary.BootstrapCompact
import PoincareLib.Geometry.CurveShortening.Comparison.RampTransport.Boundary.BootstrapComplexHessian
import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.StrictTraceHalfDisk

/-!
# A concrete finite bootstrap on the actual boundary half-ball

The successive radii are fixed fractions of the given local radius.
Actual compact closed C1 data, initial H2 and the original mixed quadratic
system give C2 on the closed half-ball of radius R/16.
Source: MT Lemma 19.31, pp. 464-466, finite boundary-bootstrap derivation,
Section 7, compact closed C1 input.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory Metric Complex
open scoped ContDiff ENNReal Topology

namespace PoincareMT.M64.RampTransport

open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Euclidean (MemWkp)
open BoundaryTangential

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Half" => halfSpace 2

/-- The actual open normal-coordinate half-ball. Source: MT Lemma 19.31 finite boundary
bootstrap, derivation Section 7. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466;
project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
def boundaryHalfBall (R : ℝ) : Set Plane := ball 0 R ∩ Half

/-- The actual compact closed normal-coordinate half-ball. Source: MT Lemma 19.31 finite
boundary bootstrap, derivation Section 7. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
def boundaryClosedHalfBall (R : ℝ) : Set Plane :=
  closedBall 0 R ∩ {z : Plane | 0 ≤ z 0}

/-- The source isometry sends coordinate zero to imaginary height. Source: MT Lemma 19.31
finite boundary bootstrap, derivation Section 7. Source: Morgan--Tian Lemma 19.31, printed
pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem boundaryComplexCoordinates_im (p : Plane) :
    (boundaryComplexCoordinates p).im = p 0 := by
  simp [boundaryComplexCoordinates, LinearIsometryEquiv.trans_apply,
    Complex.orthonormalBasisOneI_repr_symm_apply, m64BoundaryCoordinateSwap_apply]

/-- The literal open complex half-disk pulls back to the normal half-ball. Source: MT Lemma
19.31 finite boundary bootstrap, derivation Section 7. Source: Morgan--Tian Lemma 19.31,
printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem boundaryComplexCoordinates_preimage_open (R : ℝ) :
    boundaryComplexCoordinates ⁻¹' (ball (0 : ℂ) R ∩ {z | 0 < z.im}) =
      boundaryHalfBall R := by
  ext p
  simp only [mem_preimage, mem_inter_iff, mem_ball_zero_iff, boundaryComplexCoordinates.norm_map,
    mem_ofPred_eq, boundaryComplexCoordinates_im, boundaryHalfBall, halfSpace]

/-- The literal closed complex half-disk pulls back to the closed normal half-ball. Source:
MT Lemma 19.31 boundary bootstrap, derivation Section 7. Source: Morgan--Tian Lemma 19.31,
printed pp. 464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem boundaryComplexCoordinates_preimage_closed (R : ℝ) :
    boundaryComplexCoordinates ⁻¹' (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) =
      boundaryClosedHalfBall R := by
  ext p
  simp only [mem_preimage, mem_inter_iff, mem_closedBall_zero_iff,
    boundaryComplexCoordinates.norm_map, mem_ofPred_eq, boundaryComplexCoordinates_im,
    boundaryClosedHalfBall]

/-- The actual normal half-ball has the same closed differential domain as its complex
isometric image. Source: MT Lemma 19.31 finite boundary bootstrap, derivation Section 7 and
the existing complex half-disk theorem. Source: Morgan--Tian Lemma 19.31, printed pp.
464-466; project derivation
`proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem boundaryHalfBall_geometry {R : ℝ} (hR : 0 < R) :
    IsOpen (boundaryHalfBall R) ∧ Convex ℝ (boundaryHalfBall R) ∧
      IsCompact (boundaryClosedHalfBall R) ∧
      UniqueDiffOn ℝ (boundaryClosedHalfBall R) ∧
      closure (boundaryHalfBall R) = boundaryClosedHalfBall R := by
  have hhalf : Convex ℝ Half :=
    (convex_Ioi (0 : ℝ)).linear_preimage (EuclideanSpace.proj (𝕜 := ℝ) 0).toLinearMap
  refine ⟨isOpen_ball.inter isOpen_halfSpace, (convex_ball (0 : Plane) R).inter hhalf,
    (isCompact_closedBall (0 : Plane) R).inter_right
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous), ?_, ?_⟩
  · rw [← boundaryComplexCoordinates_preimage_closed]
    exact boundaryComplexCoordinates.toContinuousLinearEquiv.uniqueDiffOn_preimage_iff.mpr
      (M65StrictTrace.halfDisk_differential_domain hR).2.2.1
  · rw [← boundaryComplexCoordinates_preimage_open]
    change closure (boundaryComplexCoordinates.toHomeomorph ⁻¹'
      (ball (0 : ℂ) R ∩ {z | 0 < z.im})) = _
    rw [← boundaryComplexCoordinates.toHomeomorph.preimage_closure,
      (M65StrictTrace.halfDisk_differential_domain hR).2.2.2,
      show boundaryComplexCoordinates.toHomeomorph ⁻¹'
        (closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}) = boundaryClosedHalfBall R from
        boundaryComplexCoordinates_preimage_closed R]

variable {n : ℕ}
local notation "Target" => EuclideanSpace ℝ (Fin (n + 1))

/-- The closed C1 map with its actual H2 and mixed quadratic equation is C2 on the smaller
closed half-ball. Every intermediate regularity gain, coefficient bound and continuous
extension is produced internally. Source: MT Lemma 19.31 finite boundary bootstrap,
derivation Section 7. Source: Morgan--Tian Lemma 19.31, printed pp. 464-466; project
derivation `proof-work/tasks/M64/derivations/2026-09-27-smooth-boundary-bootstrap-plan.md`. -/
theorem mixed_quadratic_halfBall_contDiffOn_two
    {R : ℝ} (hR : 0 < R) {T : Set Target} (hT : IsOpen T)
    {u : Plane → Target}
    {B : Fin (n + 1) → Target → Target →L[ℝ] Target →L[ℝ] ℝ}
    (hc : ContDiffOn ℝ 1 u (boundaryClosedHalfBall R))
    (hs : ContDiffOn ℝ ∞ u (boundaryHalfBall R))
    (hu : ∀ j, MemWkp 2 2 (fun z => u z j) (boundaryHalfBall R))
    (hB : ∀ j, ContDiffOn ℝ 2 (B j) T)
    (huT : MapsTo u (boundaryClosedHalfBall R) T)
    (hn : ∀ z ∈ boundaryClosedHalfBall R, z 0 = 0 →
      (fderivWithin ℝ u (boundaryClosedHalfBall R) z (EuclideanSpace.single 0 1)) 0 = 0)
    (ht : ∀ j : Fin (n + 1), j ≠ 0 →
      ∀ z ∈ boundaryClosedHalfBall R, z 0 = 0 → u z j = 0)
    (heq : ∀ j z, z ∈ boundaryHalfBall R →
      -(∑ i : Fin 2, (fderiv ℝ (fderiv ℝ u) z
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) j) =
      quadraticForcing (B j) u (fun i => boundaryVectorPartial i u) z) :
    ContDiffOn ℝ 2 u (boundaryClosedHalfBall (R / 16)) := by
  have hsmall : 0 < R / 16 := by positivity
  obtain ⟨hO, hconv, hKsmall, _, hclosure⟩ := boundaryHalfBall_geometry hsmall
  have hgeom := boundaryHalfBall_geometry hR
  have hcompact (r : ℝ) : IsCompact (closure (ball (0 : Plane) r)) :=
    (isCompact_closedBall (0 : Plane) r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  have hnest {a b : ℝ} (hab : a < b) : closure (ball (0 : Plane) a) ⊆ ball 0 b :=
    closure_ball_subset_closedBall.trans (closedBall_subset_ball hab)
  rw [← hclosure]
  apply compact_mixed_quadratic_system_contDiffOn_closure hgeom.2.2.1 hgeom.2.2.2.1
    isOpen_ball (hcompact R)
    (fun _ hz => ⟨ball_subset_closedBall hz.1, hz.2⟩)
    isOpen_ball (hcompact (R / 2)) (hnest (by linarith : R / 2 < R))
    isOpen_ball (hcompact (R / 4)) (hnest (by linarith : R / 4 < R / 2))
    isOpen_ball (hcompact (R / 8)) (hnest (by linarith : R / 8 < R / 4))
    hO (hclosure.symm ▸ hKsmall) hconv inter_subset_right
    (by
      rw [hclosure]
      exact inter_subset_left.trans (closedBall_subset_ball (by linarith : R / 16 < R / 8)))
    hT hc hs hu hB huT hn ht heq

end PoincareMT.M64.RampTransport

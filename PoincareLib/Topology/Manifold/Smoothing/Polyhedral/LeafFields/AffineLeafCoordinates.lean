import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.SmoothLocalInverse
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Local coordinates along a smooth family of affine leaves

A normalized projection field along an affine base parametrizes
its kernel leaves using one fixed kernel. At the zero section,
the derivative is the complementary direct-sum equivalence, so
the inverse function theorem gives unique smooth coordinates.
See Cairns 1940, pp. 804--805, and M76 derivation 52.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Parametrize the affine kernel leaves using the kernel at one
fixed basepoint. Geometric interpretation requires normalization
on the affine frame. See Cairns pp. 804--805 and M76 derivation 52. -/
def affineLeafMap (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F) (x0 : F)
    (z : F × (Q x0).ker) : E :=
  a z.1 + (z.2 : E) - a.contLinear (Q z.1 z.2)

/-- The zero section of the affine-leaf map is its affine base.
See Cairns p. 805 and M76 derivation 52. -/
theorem affineLeafMap_zero (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 x : F) : a.affineLeafMap Q x0 (x, 0) = a x := by
  simp [affineLeafMap]

/-- The displacement of a leaf point lies in its assigned kernel.
See Cairns Hypothesis III, p. 804 and M76 derivation 52. -/
theorem affineLeafMap_sub_mem_ker (a : F →ᴬ[ℝ] E) (Q : F → E →L[ℝ] F)
    (x0 : F) (hQ : ∀ x, Function.RightInverse a.contLinear (Q x))
    (z : F × (Q x0).ker) : a.affineLeafMap Q x0 z - a z.1 ∈ (Q z.1).ker := by
  change Q z.1 (a z.1 + (z.2 : E) - a.contLinear (Q z.1 z.2) - a z.1) = 0
  rw [map_sub, map_sub, map_add, hQ]
  abel

/-- A smooth projection field gives a smooth affine-leaf map on
the fixed product space. See Cairns p. 805 and M76 derivation 52. -/
theorem contDiff_affineLeafMap (a : F →ᴬ[ℝ] E) {Q : F → E →L[ℝ] F}
    {n : ℕ∞ω} (hQ : ContDiff ℝ n Q) (x0 : F) :
    ContDiff ℝ n (a.affineLeafMap Q x0) := by
  have hz : ContDiff ℝ n (fun z : F × (Q x0).ker => (z.2 : E)) :=
    (Q x0).ker.subtypeL.contDiff.comp contDiff_snd
  exact ((a.contDiff.comp contDiff_fst).add hz).sub
    (a.contLinear.contDiff.comp ((hQ.comp contDiff_fst).clm_apply hz))

/-- At the zero section, variation of the projection field makes
no contribution to the derivative. See Cairns p. 805 and M76 derivation 52. -/
theorem hasFDerivAt_affineLeafMap_zero (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} {x0 : F} (hQ : DifferentiableAt ℝ Q x0) :
    HasFDerivAt (a.affineLeafMap Q x0)
      (a.contLinear.coprod (Q x0).ker.subtypeL) (x0, 0) := by
  let H := (Q x0).ker
  have hx : HasFDerivAt (fun z : F × H => a z.1)
      (a.contLinear.comp (ContinuousLinearMap.fst ℝ F H)) (x0, 0) :=
    a.hasFDerivAt.comp (x0, (0 : H)) (ContinuousLinearMap.fst ℝ F H).hasFDerivAt
  have hz : HasFDerivAt (fun z : F × H => (z.2 : E))
      (H.subtypeL.comp (ContinuousLinearMap.snd ℝ F H)) (x0, 0) :=
    H.subtypeL.hasFDerivAt.comp (x0, (0 : H))
      (ContinuousLinearMap.snd ℝ F H).hasFDerivAt
  have hq : HasFDerivAt (fun z : F × H => Q z.1)
      ((fderiv ℝ Q x0).comp (ContinuousLinearMap.fst ℝ F H)) (x0, 0) :=
    hQ.hasFDerivAt.comp (x0, (0 : H)) (ContinuousLinearMap.fst ℝ F H).hasFDerivAt
  have hd := (hx.add hz).sub (a.contLinear.hasFDerivAt.comp (x0, (0 : H))
    (hq.clm_apply hz))
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro z
  have hz0 : Q x0 (z.2 : E) = 0 := z.2.property
  simp [ContinuousLinearMap.coprod_apply, hz0]

variable [CompleteSpace E] [CompleteSpace F]

/-- A smooth normalized field on an affine base gives local
unique leaf coordinates with a smooth inverse throughout the
open target. See Cairns pp. 804--805 and M76 derivation 52. -/
theorem exists_smooth_affineLeaf_chart (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (hQ : ContDiff ℝ ∞ Q) (x0 : F)
    (hnorm : Function.RightInverse a.contLinear (Q x0)) :
    ∃ e : OpenPartialHomeomorph (F × (Q x0).ker) E,
      (e : F × (Q x0).ker → E) = a.affineLeafMap Q x0 ∧
      (x0, 0) ∈ e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let A := (ContinuousLinearEquiv.equivOfRightInverse (Q x0) a.contLinear hnorm).symm
  apply (a.contDiff_affineLeafMap hQ x0).exists_smooth_openPartialHomeomorph (by simp) A
  exact a.hasFDerivAt_affineLeafMap_zero (hQ.differentiable (by simp)).differentiableAt

end ContinuousAffineMap

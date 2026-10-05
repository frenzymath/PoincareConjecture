import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.InitialMetric.Rotations
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The metric on a fixed rotation axis

Morgan-Tian Lemma 12.3, pp. 294-295. At a point on the first coordinate
axis, the half turn about that axis removes radial-angular mixed terms.
The quarter turn removes the remaining angular mixed term and equates
the two angular diagonal entries. Both rotations fix the basepoint.
This is the first step of the arbitrary rotational normal form in the
arbitrary-initial-estimates derivation.
-/

set_option autoImplicit false

open Matrix
open scoped Manifold ContDiff

namespace PoincareMT.M34

/-- The orientation-preserving half turn about the first coordinate axis
(Lemma 12.3, pp. 294-295). -/
def capAxisHalfTurn : Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  refine ⟨!![1, 0, 0; 0, -1, 0; 0, 0, -1], mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩⟩
  · rw [mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  · norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

/-- The orientation-preserving quarter turn about the first coordinate
axis (Lemma 12.3, pp. 294-295). -/
def capAxisQuarterTurn : Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  refine ⟨!![1, 0, 0; 0, 0, -1; 0, 1, 0], mem_specialOrthogonalGroup_iff.mpr ⟨?_, ?_⟩⟩
  · rw [mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]
  · norm_num [Matrix.det_fin_three, Matrix.cons_val_two]

/-- The literal half-turn matrix acts by changing the two angular signs
(Lemma 12.3, pp. 294-295). -/
theorem capAxisHalfTurn_apply (x : StandardCapSpace) :
    standardRotation capAxisHalfTurn x =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x 0, -x 1, -x 2] := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  ext i
  fin_cases i <;> simp [standardRotation, capAxisHalfTurn,
    dotProduct, Fin.sum_univ_three]

/-- The literal quarter-turn matrix rotates the two angular coordinates
(Lemma 12.3, pp. 294-295). -/
theorem capAxisQuarterTurn_apply (x : StandardCapSpace) :
    standardRotation capAxisQuarterTurn x =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x 0, -x 2, x 1] := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  ext i
  fin_cases i <;> simp [standardRotation, capAxisQuarterTurn,
    dotProduct, Fin.sum_univ_three]

set_option backward.isDefEq.respectTransparency false in
/-- The supplied metric's actual rotational invariance can be evaluated
on constant ambient vectors (Lemma 12.3, pp. 294-295). -/
theorem initialMetric_inner_rotation (g₀ : StandardInitialMetric)
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x u v : StandardCapSpace) :
    g₀.metric.inner (standardRotation A x) (standardRotation A u) (standardRotation A v) =
      g₀.metric.inner x u v := by
  have h := g₀.rotation_invariant A x u v
  erw [standardRotation_mfderiv] at h
  exact h

private theorem halfTurn_single (i : Fin 3) (r : ℝ) :
    standardRotation capAxisHalfTurn (EuclideanSpace.single i r) =
      if i = 0 then EuclideanSpace.single i r else -EuclideanSpace.single i r := by
  rw [capAxisHalfTurn_apply]
  ext j
  fin_cases i <;> fin_cases j <;> simp

private theorem quarterTurn_axis (r : ℝ) :
    standardRotation capAxisQuarterTurn (EuclideanSpace.single (0 : Fin 3) r) =
      EuclideanSpace.single (0 : Fin 3) r := by
  rw [capAxisQuarterTurn_apply]
  ext j
  fin_cases j <;> simp

private theorem quarterTurn_first :
    standardRotation capAxisQuarterTurn (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) =
      EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
  rw [capAxisQuarterTurn_apply]
  ext j
  fin_cases j <;> simp

private theorem quarterTurn_second :
    standardRotation capAxisQuarterTurn (EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) =
      -EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
  rw [capAxisQuarterTurn_apply]
  ext j
  fin_cases j <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- On the fixed first axis the metric has no mixed coefficients, and
its two angular diagonal coefficients agree (Lemma 12.3, pp. 294-295). -/
theorem initialMetric_axis_coefficients (g₀ : StandardInitialMetric) (r : ℝ) :
    let x := EuclideanSpace.single (0 : Fin 3) r
    let b := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
    g₀.metric.inner x (b 0) (b 1) = 0 ∧
      g₀.metric.inner x (b 0) (b 2) = 0 ∧
      g₀.metric.inner x (b 1) (b 2) = 0 ∧
      g₀.metric.inner x (b 2) (b 2) = g₀.metric.inner x (b 1) (b 1) := by
  let x : StandardCapSpace := EuclideanSpace.single 0 r
  let b := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
  change g₀.metric.inner x (b 0) (b 1) = 0 ∧
    g₀.metric.inner x (b 0) (b 2) = 0 ∧ g₀.metric.inner x (b 1) (b 2) = 0 ∧
    g₀.metric.inner x (b 2) (b 2) = g₀.metric.inner x (b 1) (b 1)
  have hxH : standardRotation capAxisHalfTurn x = x := by simp [x, halfTurn_single]
  have hbH0 : standardRotation capAxisHalfTurn (b 0) = b 0 := by simp [b, halfTurn_single]
  have hbH1 : standardRotation capAxisHalfTurn (b 1) = -b 1 := by simp [b, halfTurn_single]
  have hbH2 : standardRotation capAxisHalfTurn (b 2) = -b 2 := by simp [b, halfTurn_single]
  have h01 := initialMetric_inner_rotation g₀ capAxisHalfTurn x (b 0) (b 1)
  have h02 := initialMetric_inner_rotation g₀ capAxisHalfTurn x (b 0) (b 2)
  erw [hxH, hbH0, hbH1, map_neg] at h01
  erw [hxH, hbH0, hbH2, map_neg] at h02
  have hxQ : standardRotation capAxisQuarterTurn x = x := quarterTurn_axis r
  have h12 := initialMetric_inner_rotation g₀ capAxisQuarterTurn x (b 1) (b 2)
  erw [hxQ, quarterTurn_first, quarterTurn_second, map_neg] at h12
  have hsym := g₀.metric.symm x (b 2) (b 1)
  have h22 := initialMetric_inner_rotation g₀ capAxisQuarterTurn x (b 1) (b 1)
  erw [hxQ, quarterTurn_first] at h22
  exact ⟨by linarith, by linarith, by linarith, h22⟩

set_option backward.isDefEq.respectTransparency false in
/-- The complete bilinear form at an axis point has one radial coefficient
and a common angular coefficient (Lemma 12.3, pp. 294-295). -/
theorem initialMetric_axis_inner (g₀ : StandardInitialMetric) (r : ℝ)
    (u v : StandardCapSpace) :
    let x := EuclideanSpace.single (0 : Fin 3) r
    let b := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
    g₀.metric.inner x u v = g₀.metric.inner x (b 0) (b 0) * u 0 * v 0 +
      g₀.metric.inner x (b 1) (b 1) * (u 1 * v 1 + u 2 * v 2) := by
  let x : StandardCapSpace := EuclideanSpace.single 0 r
  let b := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)
  obtain ⟨h01, h02, h12, h22⟩ := initialMetric_axis_coefficients g₀ r
  change g₀.metric.inner x (b 0) (b 1) = 0 at h01
  change g₀.metric.inner x (b 0) (b 2) = 0 at h02
  change g₀.metric.inner x (b 1) (b 2) = 0 at h12
  change g₀.metric.inner x (b 2) (b 2) = g₀.metric.inner x (b 1) (b 1) at h22
  have h10 : g₀.metric.inner x (b 1) (b 0) = 0 :=
    (g₀.metric.symm x (b 1) (b 0)).trans h01
  have h20 : g₀.metric.inner x (b 2) (b 0) = 0 :=
    (g₀.metric.symm x (b 2) (b 0)).trans h02
  have h21 : g₀.metric.inner x (b 2) (b 1) = 0 :=
    (g₀.metric.symm x (b 2) (b 1)).trans h12
  have hsum (w : StandardCapSpace) : ∑ i, w i • b i = w := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := g₀.metric.inner x
  change B (b 0) (b 1) = 0 at h01
  change B (b 0) (b 2) = 0 at h02
  change B (b 1) (b 2) = 0 at h12
  change B (b 1) (b 0) = 0 at h10
  change B (b 2) (b 0) = 0 at h20
  change B (b 2) (b 1) = 0 at h21
  change B (b 2) (b 2) = B (b 1) (b 1) at h22
  change B u v = B (b 0) (b 0) * u 0 * v 0 +
    B (b 1) (b 1) * (u 1 * v 1 + u 2 * v 2)
  calc
    B u v = B (∑ i, u i • b i) (∑ i, v i • b i) := by rw [hsum, hsum]
    _ = _ := by
      simp only [map_add, _root_.add_apply, map_smul, _root_.smul_apply, smul_eq_mul,
        Fin.sum_univ_three, h01, h02, h12, h10, h20, h21, h22]
      ring

end PoincareMT.M34

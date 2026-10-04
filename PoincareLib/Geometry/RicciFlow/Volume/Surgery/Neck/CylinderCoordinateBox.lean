import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Neck.NeckCoordinates
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Analysis.EuclideanBox

/-!
Adapted from Mapher `PoincareMT/Proofs/M49/CylinderCoordinateBox.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# A fixed-area box in cylinder coordinates

Morgan-Tian Definition 2.18, p. 31, and Lemma 17.12, p. 410. The first
two coordinate intervals lie strictly inside the specified sphere-chart
ball. The line interval has its full displayed length.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace PoincareMT.SurgeryVolume

/-- A fixed square of side `r`, extended along the positive line interval
(MT Definition 2.18, p. 31; Lemma 17.12, p. 410). -/
def cylinderCoordinateBox (p : EuclideanSpace ℝ (Fin 2)) (r t : ℝ) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | x 0 ∈ Ioo (p 0 - r / 2) (p 0 + r / 2) ∧
    x 1 ∈ Ioo (p 1 - r / 2) (p 1 + r / 2) ∧ x 2 ∈ Ioo 0 t}

/-- The coordinate box is open, including when an interval is empty
(MT Lemma 17.12, p. 410, coordinate-integration expansion). -/
theorem isOpen_cylinderCoordinateBox (p : EuclideanSpace ℝ (Fin 2)) (r t : ℝ) :
    IsOpen (cylinderCoordinateBox p r t) := by
  exact (isOpen_Ioo.preimage (by fun_prop : Continuous
    (fun x : EuclideanSpace ℝ (Fin 3) => x 0))).inter
      ((isOpen_Ioo.preimage (by fun_prop : Continuous
        (fun x : EuclideanSpace ℝ (Fin 3) => x 1))).inter
          (isOpen_Ioo.preimage (by fun_prop : Continuous
            (fun x : EuclideanSpace ℝ (Fin 3) => x 2))))

/-- The coordinate box has its square area times its positive line length
(MT Lemma 17.12, p. 410); nonpositive line lengths give an empty box. -/
theorem volume_cylinderCoordinateBox (p : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 ≤ r) (t : ℝ) :
    volume (cylinderCoordinateBox p r t) = ENNReal.ofReal (r ^ 2 * t) := by
  let a : Fin 3 → ℝ := ![p 0 - r / 2, p 1 - r / 2, 0]
  let b : Fin 3 → ℝ := ![p 0 + r / 2, p 1 + r / 2, t]
  have hset : cylinderCoordinateBox p r t =
      {x : EuclideanSpace ℝ (Fin 3) | ∀ i, x i ∈ Ioo (a i) (b i)} := by
    ext x
    simp [cylinderCoordinateBox, a, b, Fin.forall_fin_succ]
  rw [hset, EuclideanSpace.volume_coordinate_Ioo]
  have h0 : b 0 - a 0 = r := by dsimp [a, b]; ring
  have h1 : b 1 - a 1 = r := by dsimp [a, b]; ring
  have h2 : b 2 - a 2 = t := by simp [a, b]
  rw [Fin.prod_univ_three, h0, h1, h2, ← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_mul (mul_nonneg hr hr)]
  congr 1
  ring

/-- The square of side `r` lies strictly inside the actual Euclidean
two-dimensional radius-`r` ball (MT Definition 2.18, p. 31). -/
theorem cylinderCoordinateBox_subset (p : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) (t : ℝ) :
    cylinderCoordinateBox p r t ⊆ cylinderCoordinateEquiv ⁻¹'
      (Metric.ball p r ×ˢ Ioo 0 t) := by
  intro x hx
  rcases hx with ⟨h0, h1, h2⟩
  have hsq0 : (x 0 - p 0) ^ 2 < (r / 2) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h0.1) (sub_pos.mpr h0.2)]
  have hsq1 : (x 1 - p 1) ^ 2 < (r / 2) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr h1.1) (sub_pos.mpr h1.2)]
  have hnorm : ‖(cylinderCoordinateEquiv x).1 - p‖ ^ 2 =
      (x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, cylinderCoordinateEquiv_apply]
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    nlinarith [norm_nonneg ((cylinderCoordinateEquiv x).1 - p)]
  · simpa only [cylinderCoordinateEquiv_apply] using h2

end PoincareMT.SurgeryVolume

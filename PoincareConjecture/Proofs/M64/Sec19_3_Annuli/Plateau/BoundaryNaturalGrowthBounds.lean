import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryPotentialBound

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

local instance m64BoundaryBounds_bilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryBounds_bilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance m64BoundaryBounds_trilinearGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance m64BoundaryBounds_trilinearSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem m64Bilinear_norm_bound (G : E →L[ℝ] E →L[ℝ] ℝ)
    {C : ℝ} (hG : ‖G‖ ≤ C) (v w : E) : |G v w| ≤ C * ‖v‖ * ‖w‖ := by
  calc
    _ ≤ ‖G v‖ * ‖w‖ := (G v).le_opNorm w
    _ ≤ (‖G‖ * ‖v‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (G.le_opNorm v) (norm_nonneg _)
    _ ≤ _ := by gcongr

theorem m64WeightedBoundary_principal_bound
    (G : E →L[ℝ] E →L[ℝ] ℝ) (w : Fin 2 → ℝ) (V D : Fin 2 → E)
    {kappa mu C Lambda : ℝ} (hk : 0 < kappa) (hmu : 0 < mu)
    (hG : ‖G‖ ≤ C) (hpos : ∀ v : E, kappa * ‖v‖ ^ 2 ≤ G v v)
    (hw : ∀ i, mu ≤ w i ∧ w i ≤ Lambda) :
    kappa * mu / 2 * (∑ i : Fin 2, ‖V i‖ ^ 2) -
      (C ^ 2 * Lambda ^ 2 / (2 * (kappa * mu))) * ∑ i : Fin 2, ‖D i‖ ^ 2 ≤
      ∑ i : Fin 2, w i * G (V i) (V i - D i) := by
  have hC : 0 ≤ C := (norm_nonneg G).trans hG
  have hL : 0 < Lambda := hmu.trans_le ((hw 0).1.trans (hw 0).2)
  have hpoint (i : Fin 2) : kappa * mu / 2 * ‖V i‖ ^ 2 -
      (C ^ 2 * Lambda ^ 2 / (2 * (kappa * mu))) * ‖D i‖ ^ 2 ≤
        w i * G (V i) (V i - D i) := by
    have hwi : 0 ≤ w i := hmu.le.trans (hw i).1
    have hdiag : kappa * mu * ‖V i‖ ^ 2 ≤ w i * G (V i) (V i) := by
      calc
        _ = mu * (kappa * ‖V i‖ ^ 2) := by ring
        _ ≤ w i * (kappa * ‖V i‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (hw i).1 (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hpos _) hwi
    have hcross : w i * G (V i) (D i) ≤ Lambda * (C * ‖V i‖ * ‖D i‖) := by
      calc
        _ ≤ w i * |G (V i) (D i)| := mul_le_mul_of_nonneg_left (le_abs_self _) hwi
        _ ≤ w i * (C * ‖V i‖ * ‖D i‖) :=
          mul_le_mul_of_nonneg_left (m64Bilinear_norm_bound G hG _ _) hwi
        _ ≤ _ := mul_le_mul_of_nonneg_right (hw i).2 (by positivity)
    have hyoung : 2 * (Lambda * (C * ‖V i‖ * ‖D i‖)) ≤
        kappa * mu * ‖V i‖ ^ 2 +
          (C ^ 2 * Lambda ^ 2 / (kappa * mu)) * ‖D i‖ ^ 2 := by
      apply two_mul_le_add_of_sq_le_mul (by positivity) (by positivity)
      apply le_of_eq
      field_simp
    rw [map_sub, mul_sub]
    have hfactor : C ^ 2 * Lambda ^ 2 / (kappa * mu) =
        2 * (C ^ 2 * Lambda ^ 2 / (2 * (kappa * mu))) := by ring
    rw [hfactor] at hyoung
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) => hpoint i)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum] using hsum

theorem m64WeightedBoundary_cross_bound
    (G : E →L[ℝ] E →L[ℝ] ℝ) (w : Fin 2 → ℝ) (V : Fin 2 → E)
    (v : E) (d : Fin 2 → ℝ) {C Lambda : ℝ}
    (hG : ‖G‖ ≤ C) (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Lambda) :
    (∑ i : Fin 2, w i * G (V i) v * d i) ^ 2 ≤
      C ^ 2 * Lambda ^ 2 * ‖v‖ ^ 2 * (∑ i : Fin 2, ‖V i‖ ^ 2) *
        ∑ i : Fin 2, d i ^ 2 := by
  have hC : 0 ≤ C := (norm_nonneg G).trans hG
  have hL : 0 ≤ Lambda := (hw 0).1.trans (hw 0).2
  have hsq (i : Fin 2) : (w i * G (V i) v) ^ 2 ≤
      C ^ 2 * Lambda ^ 2 * ‖v‖ ^ 2 * ‖V i‖ ^ 2 := by
    have hb : |w i * G (V i) v| ≤ Lambda * (C * ‖V i‖ * ‖v‖) := by
      rw [abs_mul, abs_of_nonneg (hw i).1]
      exact (mul_le_mul_of_nonneg_left (m64Bilinear_norm_bound G hG _ _) (hw i).1).trans
        (mul_le_mul_of_nonneg_right (hw i).2 (by positivity))
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
    simpa only [sq_abs, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hh
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 2))) => hsq i)
  rw [← Finset.mul_sum] at hsum
  exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => w i * G (V i) v) d).trans
    (mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem m64Trilinear_norm_bound (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ)
    {C : ℝ} (hT : ‖T‖ ≤ C) (v w : E) : |T v w w| ≤ C * ‖v‖ * ‖w‖ ^ 2 := by
  calc
    _ ≤ ‖T v w‖ * ‖w‖ := (T v w).le_opNorm w
    _ ≤ (‖T v‖ * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right ((T v).le_opNorm w) (norm_nonneg _)
    _ ≤ ((‖T‖ * ‖v‖) * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ ((C * ‖v‖) * ‖w‖) * ‖w‖ := by gcongr
    _ = _ := by ring

theorem m64WeightedBoundary_source_bound
    (T : E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (w : Fin 2 → ℝ) (V : Fin 2 → E)
    (v : E) {C Lambda : ℝ} (hT : ‖T‖ ≤ C)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Lambda) :
    |-(∑ i : Fin 2, w i * T v (V i) (V i)) / 2| ≤
      C * Lambda * ‖v‖ * (∑ i : Fin 2, ‖V i‖ ^ 2) / 2 := by
  have hC : 0 ≤ C := (norm_nonneg T).trans hT
  have hb (i : Fin 2) : |w i * T v (V i) (V i)| ≤ Lambda *
      (C * ‖v‖ * ‖V i‖ ^ 2) := by
    rw [abs_mul, abs_of_nonneg (hw i).1]
    exact (mul_le_mul_of_nonneg_left (m64Trilinear_norm_bound T hT _ _) (hw i).1).trans
      (mul_le_mul_of_nonneg_right (hw i).2 (by positivity))
  have hsum := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
    (Finset.sum_le_sum (fun i _ => hb i))
  rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply div_le_div_of_nonneg_right ?_ (by norm_num)
  exact hsum.trans_eq (by simp only [← Finset.mul_sum]; ring)

end PoincareConjecture

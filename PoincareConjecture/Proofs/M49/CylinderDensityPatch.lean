import PoincareConjecture.Proofs.M49.CylinderDensity
import PoincareConjecture.Proofs.M49.Mathlib.GramDensity
import Mathlib.Analysis.Matrix.PosDef









set_option autoImplicit false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M49




theorem exists_cylinder_density_patch (q : UnitTwoSphere) :
    ∃ r d a : ℝ, 0 < r ∧ 0 < d ∧ 0 < a ∧
      ∀ p : RoundCylinderCoordinates,
        p.1 ∈ Metric.ball ((chartAt (EuclideanSpace ℝ (Fin 2)) q) q) r →
        p.1 ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ∧
        ∀ A : Matrix (Fin 3) (Fin 3) ℝ,
          (∀ i j, |A i j - roundCylinderGram 0
              (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j| ≤
            d * Real.sqrt (roundCylinderGram 0
              (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i i) *
              Real.sqrt (roundCylinderGram 0
                (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j j)) →
          a ≤ Real.sqrt A.det := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let p0 : RoundCylinderCoordinates := (c q, 0)
  let G0 := roundCylinderGram 0 c p0
  have hcq : c q ∈ c.target := c.map_source (mem_chart_source _ _)
  have hG0 : G0.PosDef := roundCylinderGram_posDef 0 (by norm_num) q p0 hcq
  have hJ : 0 < Real.sqrt G0.det := Real.sqrt_pos.2 hG0.det_pos
  obtain ⟨eta, heta, htol⟩ := Matrix.exists_pos_entrywise_sqrt_det_lower G0 hJ
  let L : ℝ := 1 + ∑ i : Fin 3, |G0 i i|
  have hsum : 0 ≤ ∑ i : Fin 3, |G0 i i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hL : 0 < L := by dsimp [L]; linarith
  have hcont : ContinuousAt (fun x : EuclideanSpace ℝ (Fin 2) =>
      roundCylinderGram 0 c (x, 0)) (c q) :=
    (continuousAt_roundCylinderGram 0 q (p := p0) hcq).comp
      (f := fun x : EuclideanSpace ℝ (Fin 2) => (x, (0 : ℝ)))
      (continuousAt_id.prodMk continuousAt_const)
  have htolpos : 0 < min (eta / 2) 1 := lt_min (half_pos heta) zero_lt_one
  obtain ⟨s, hs, hnear⟩ := (Metric.continuousAt_iff
    (α := EuclideanSpace ℝ (Fin 2)) (β := Fin 3 → Fin 3 → ℝ)).mp hcont _ htolpos
  obtain ⟨t, ht, htarget⟩ := Metric.mem_nhds_iff.mp (c.open_target.mem_nhds hcq)
  refine ⟨min s t, eta / (2 * L), Real.sqrt G0.det / 2,
    lt_min hs ht, div_pos heta (mul_pos (by norm_num) hL), half_pos hJ, ?_⟩
  intro p hp
  have hps : dist p.1 (c q) < s := (Metric.mem_ball.mp hp).trans_le (min_le_left _ _)
  have hpt : p.1 ∈ c.target :=
    htarget ((Metric.mem_ball.mp hp).trans_le (min_le_right _ _))
  refine ⟨hpt, ?_⟩
  have hclose (i j : Fin 3) :
      |roundCylinderGram 0 c p i j - G0 i j| < min (eta / 2) 1 := by
    have houter := dist_le_pi_dist
      (show Fin 3 → Fin 3 → ℝ from roundCylinderGram 0 c (p.1, 0)) G0 i
    have hinner := dist_le_pi_dist
      (roundCylinderGram 0 c (p.1, 0) i) (G0 i) j
    have hi := (hinner.trans houter).trans_lt (hnear hps)
    rw [Real.dist_eq] at hi
    simpa only [roundCylinderGram_eq_zero_line] using hi
  have hdiag (i : Fin 3) : roundCylinderGram 0 c p i i ≤ L := by
    have he := (abs_lt.mp ((hclose i i).trans_le (min_le_right _ _))).2
    have hi : |G0 i i| ≤ ∑ j : Fin 3, |G0 j j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (G0 j j)) (Finset.mem_univ i)
    have hi0 := le_abs_self (G0 i i)
    dsimp [L]
    linarith
  intro A hA
  apply htol A
  intro i j
  have hsqrt : Real.sqrt (roundCylinderGram 0 c p i i) *
      Real.sqrt (roundCylinderGram 0 c p j j) ≤ L := by
    calc
      _ ≤ Real.sqrt L * Real.sqrt L := mul_le_mul
        (Real.sqrt_le_sqrt (hdiag i)) (Real.sqrt_le_sqrt (hdiag j))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = L := Real.mul_self_sqrt hL.le
  have herror : |A i j - roundCylinderGram 0 c p i j| ≤ eta / 2 := by
    calc
      _ ≤ eta / (2 * L) * Real.sqrt (roundCylinderGram 0 c p i i) *
          Real.sqrt (roundCylinderGram 0 c p j j) := hA i j
      _ = eta / (2 * L) * (Real.sqrt (roundCylinderGram 0 c p i i) *
          Real.sqrt (roundCylinderGram 0 c p j j)) := mul_assoc _ _ _
      _ ≤ eta / (2 * L) * L := mul_le_mul_of_nonneg_left hsqrt
        (div_nonneg heta.le (mul_nonneg (by norm_num) hL.le))
      _ = eta / 2 := by field_simp
  have hmodel := ((hclose i j).trans_le (min_le_left _ _)).le
  calc
    |A i j - G0 i j| ≤ |A i j - roundCylinderGram 0 c p i j| +
        |roundCylinderGram 0 c p i j - G0 i j| := abs_sub_le _ _ _
    _ ≤ eta := by linarith

end PoincareConjecture.M49

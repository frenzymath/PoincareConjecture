import PoincareConjecture.Proofs.M35.RadialGauge.TipForcing











set_option autoImplicit false

open scoped ContDiff

namespace PoincareConjecture.M35.RadialGauge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def semilinearSource (b : E) (G : ℝ → ℝ)
    (u : ℝ) (p : E →L[ℝ] ℝ) : ℝ := p b + ‖p‖ ^ 2 + G u



theorem semilinearSource_weighted_bound
    {w eta B L C u : ℝ} (hw : 1 ≤ w) (heta : 0 ≤ eta)
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (b : E) (G : ℝ → ℝ) (p : E →L[ℝ] ℝ)
    (hb : ‖b‖ ≤ B) (hu : w * |u| ≤ eta) (hp : w * ‖p‖ ≤ eta)
    (hGzero : w * |G 0| ≤ C) (hGlip : |G u - G 0| ≤ L * |u|) :
    w * |semilinearSource b G u p| ≤ B * eta + eta ^ 2 + L * eta + C := by
  have hw0 : 0 ≤ w := le_trans zero_le_one hw
  have hple : ‖p‖ ≤ eta :=
    (le_mul_of_one_le_left (norm_nonneg _) hw).trans hp
  have hpb : |p b| ≤ ‖p‖ * B :=
    (p.le_opNorm b).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  have hgradient : w * ‖p‖ ^ 2 ≤ eta ^ 2 := by
    calc
      _ = (w * ‖p‖) * ‖p‖ := by ring
      _ ≤ eta * eta := mul_le_mul hp hple (norm_nonneg _) heta
      _ = _ := by ring
  have hforcing : w * |G u| ≤ L * eta + C := by
    have htriangle : |G u| ≤ |G u - G 0| + |G 0| := by
      simpa only [sub_add_cancel] using abs_add_le (G u - G 0) (G 0)
    have h := mul_le_mul_of_nonneg_left (htriangle.trans
      (add_le_add hGlip le_rfl)) hw0
    have hlu := mul_le_mul_of_nonneg_left hu hL
    nlinarith
  have hsource : |semilinearSource b G u p| ≤ |p b| + ‖p‖ ^ 2 + |G u| := by
    unfold semilinearSource
    calc
      _ ≤ |p b + ‖p‖ ^ 2| + |G u| := abs_add_le _ _
      _ ≤ _ := add_le_add (by
        have htriangle := abs_add_le (p b) (‖p‖ ^ 2)
        rw [abs_of_nonneg (sq_nonneg ‖p‖)] at htriangle
        exact htriangle) le_rfl
  have h := mul_le_mul_of_nonneg_left hsource hw0
  have hpB := mul_le_mul_of_nonneg_left hp hB
  have hpbw := mul_le_mul_of_nonneg_left hpb hw0
  nlinarith



theorem norm_sq_sub_norm_sq_le (p q : E →L[ℝ] ℝ) :
    |‖p‖ ^ 2 - ‖q‖ ^ 2| ≤ (‖p‖ + ‖q‖) * ‖p - q‖ := by
  calc
    _ = |‖p‖ - ‖q‖| * (‖p‖ + ‖q‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg p) (norm_nonneg q)), ← abs_mul]
      congr 1
      ring
    _ ≤ ‖p - q‖ * (‖p‖ + ‖q‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le p q)
        (add_nonneg (norm_nonneg p) (norm_nonneg q))
    _ = _ := mul_comm _ _




theorem semilinearSource_weighted_lipschitz
    {w eta B L u v : ℝ} (hw : 1 ≤ w)
    (b : E) (G : ℝ → ℝ) (p q : E →L[ℝ] ℝ)
    (hb : ‖b‖ ≤ B) (hp : w * ‖p‖ ≤ eta) (hq : w * ‖q‖ ≤ eta)
    (hGlip : |G u - G v| ≤ L * |u - v|) :
    w * |semilinearSource b G u p - semilinearSource b G v q| ≤
      L * (w * |u - v|) + (B + 2 * eta) * (w * ‖p - q‖) := by
  have hw0 : 0 ≤ w := le_trans zero_le_one hw
  have hple : ‖p‖ ≤ eta :=
    (le_mul_of_one_le_left (norm_nonneg _) hw).trans hp
  have hqle : ‖q‖ ≤ eta :=
    (le_mul_of_one_le_left (norm_nonneg _) hw).trans hq
  have hpb : |p b - q b| ≤ B * ‖p - q‖ := by
    have h := (p - q).le_opNorm b
    change |p b - q b| ≤ ‖p - q‖ * ‖b‖ at h
    exact h.trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq (mul_comm _ _))
  have hsq : |‖p‖ ^ 2 - ‖q‖ ^ 2| ≤ 2 * eta * ‖p - q‖ :=
    (norm_sq_sub_norm_sq_le p q).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  have hsource : |semilinearSource b G u p - semilinearSource b G v q| ≤
      |p b - q b| + |‖p‖ ^ 2 - ‖q‖ ^ 2| + |G u - G v| := by
    unfold semilinearSource
    calc
      _ = |(p b - q b) + (‖p‖ ^ 2 - ‖q‖ ^ 2) + (G u - G v)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  have h := mul_le_mul_of_nonneg_left
    (hsource.trans (add_le_add (add_le_add hpb hsq) hGlip)) hw0
  nlinarith

end PoincareConjecture.M35.RadialGauge

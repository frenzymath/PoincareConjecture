import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFamilySelection










set_option autoImplicit false

open Set Filter

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}



theorem base_scalar_pos (H : CounterexampleNeckFamily E) (k : ℕ) :
    0 < (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩ :=
  lt_of_lt_of_le (by positivity) (E (k + H.shift)).base_lower



theorem base_scalar_tendsto_atTop (H : CounterexampleNeckFamily E) :
    Tendsto (fun k => (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) atTop atTop :=
  (counterexampleBlowupSequence E).scalar_diverges.comp
    H.sourceIndex_strictMono.tendsto_atTop



theorem lower_scalar_pos (H : CounterexampleNeckFamily E) (k : ℕ) :
    0 < (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩ := by
  rw [(H.segment k).lower_scalar]
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hB)) (H.base_scalar_pos k)



theorem lower_scalar_tendsto_atTop (H : CounterexampleNeckFamily E) :
    Tendsto (fun k => (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩)
      atTop atTop := by
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have h := (tendsto_const_mul_atTop_of_pos
    (mul_pos (by norm_num : (0 : ℝ) < 16) (sq_pos_of_pos hB))).2
      H.base_scalar_tendsto_atTop
  convert h using 1
  funext k
  exact (H.segment k).lower_scalar



theorem retained_ratio_lower (H : CounterexampleNeckFamily E) (k : ℕ) :
    (((k + H.shift : ℕ) : ℝ) + 1) / (32 * (max C 2) ^ 4) <
      (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).upper⟩ /
        (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩ := by
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  apply (div_lt_div_iff₀ (by positivity : 0 < 32 * (max C 2) ^ 4)
    (H.lower_scalar_pos k)).2
  rw [(H.segment k).lower_scalar]
  have h := mul_lt_mul_of_pos_left (H.segment k).upper_scalar
    (mul_pos (by norm_num : (0 : ℝ) < 16) (sq_pos_of_pos hB))
  nlinarith only [h]



theorem retained_ratio_tendsto_atTop (H : CounterexampleNeckFamily E) :
    Tendsto (fun k =>
      (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).upper⟩ /
        (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩)
      atTop atTop := by
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hindex : Tendsto (fun k : ℕ => ((k + H.shift : ℕ) : ℝ) + 1)
      atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ)) _ tendsto_natCast_atTop_atTop
    intro k
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) H.shift]
  exact tendsto_atTop_mono (fun k => (H.retained_ratio_lower k).le)
    ((tendsto_div_const_atTop_of_pos
      (by positivity : 0 < 32 * (max C 2) ^ 4)).2 hindex)



theorem neck_center_scalar_tendsto_atTop (H : CounterexampleNeckFamily E)
    (v : ℕ → ℝ) (hv : ∀ k, v k ∈ Icc (H.segment k).lower (H.segment k).upper) :
    Tendsto (fun k => (E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, ((H.segment k).neckAt (v k) (hv k)).center⟩)
      atTop atTop := by
  apply tendsto_atTop_mono (f := fun k => (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (H.segment k).path (H.segment k).lower⟩)
      _ H.lower_scalar_tendsto_atTop
  intro k
  rw [(H.segment k).neckAt_center, (H.segment k).lower_scalar]
  exact ((H.segment k).scalar_band (v k) (hv k)).1

end PoincareConjecture.M28.CounterexampleNeckFamily

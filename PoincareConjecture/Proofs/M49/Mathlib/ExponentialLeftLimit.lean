import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Monotone









set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal

namespace ENNReal



theorem antitoneOn_exp_weight_of_growth {f : ℝ → ℝ≥0∞} {s : Set ℝ} {k : ℝ}
    (h : ∀ a ∈ s, ∀ b ∈ s, a ≤ b →
      f b ≤ ENNReal.ofReal (Real.exp (k * (b - a))) * f a) :
    AntitoneOn (fun t => ENNReal.ofReal (Real.exp (-(k * t))) * f t) s := by
  intro a ha b hb hab
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(k * b))) *
        (ENNReal.ofReal (Real.exp (k * (b - a))) * f a) :=
      mul_le_mul_right (h a ha b hb hab) _
    _ = _ := by
      rw [← mul_assoc, ← ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      have he : -(k * b) + k * (b - a) = -(k * a) := by ring
      rw [he]



theorem exists_finite_left_limit_of_exp_growth {f : ℝ → ℝ≥0∞} {a T k : ℝ}
    (haT : a < T) (hfa : f a ≠ ⊤)
    (h : ∀ s ∈ Ico a T, ∀ t ∈ Ico a T, s ≤ t →
      f t ≤ ENNReal.ofReal (Real.exp (k * (t - s))) * f s) :
    ∃ L : ℝ≥0∞, L ≠ ⊤ ∧ Tendsto f (𝓝[<] T) (𝓝 L) := by
  let w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(k * t))) * f t
  have hw : AntitoneOn w (Ico a T) := antitoneOn_exp_weight_of_growth h
  let c := (a + T) / 2
  have hc : c ∈ Ioo a T := by dsimp [c]; constructor <;> linarith
  have hfc : f c < ⊤ :=
    (h a ⟨le_rfl, haT⟩ c ⟨hc.1.le, hc.2⟩ hc.1.le).trans_lt
      (mul_lt_top ofReal_lt_top (lt_top_iff_ne_top.mpr hfa))
  let Lw := sInf (w '' Ioo a T)
  have hLw : Lw < ⊤ :=
    (sInf_le (mem_image_of_mem w hc)).trans_lt (mul_lt_top ofReal_lt_top hfc)
  have hlim : Tendsto w (𝓝[<] T) (𝓝 Lw) :=
    (hw.mono Ioo_subset_Ico_self).tendsto_nhdsWithin_Ioo_left ⟨c, hc⟩
      ⟨0, fun _ _ => bot_le⟩
  have hexp : Continuous (fun t : ℝ => ENNReal.ofReal (Real.exp (k * t))) :=
    continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  refine ⟨ENNReal.ofReal (Real.exp (k * T)) * Lw, mul_ne_top ofReal_ne_top hLw.ne, ?_⟩
  have hprod := ENNReal.Tendsto.mul
    ((hexp.tendsto T).mono_left nhdsWithin_le_nhds) (Or.inr hLw.ne)
    hlim (Or.inr ofReal_ne_top)
  have heq (t : ℝ) : ENNReal.ofReal (Real.exp (k * t)) * w t = f t := by
    dsimp [w]
    rw [← mul_assoc, ← ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      add_neg_cancel, Real.exp_zero, ofReal_one, one_mul]
  simpa only [heq] using hprod

end ENNReal

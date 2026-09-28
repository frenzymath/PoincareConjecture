import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set MeasureTheory
open scoped intervalIntegral Topology

theorem ContinuousOn.antitoneOn_Icc_of_antitoneOn_Ioo
    {B : Type*} [TopologicalSpace B] [Preorder B] [OrderClosedTopology B]
    {f : ℝ → B} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hanti : AntitoneOn f (Ioo a b)) : AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  obtain rfl | hxy := hxy.eq_or_lt
  · exact le_rfl
  have hyz : ∀ z ∈ Ioo x y, f y ≤ f z := by
    intro z hz
    have hclose : y ∈ closure (Ioo z y) := by
      rw [closure_Ioo hz.2.ne]
      exact ⟨hz.2.le, le_rfl⟩
    exact ContinuousWithinAt.closure_le hclose
      ((hf y hy).mono (fun w hw => ⟨hx.1.trans (hz.1.le.trans hw.1.le), hw.2.le.trans hy.2⟩))
      continuousWithinAt_const
      (fun w hw => hanti ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
        ⟨hx.1.trans_lt (hz.1.trans hw.1), hw.2.trans_le hy.2⟩ hw.1.le)
  have hclose : x ∈ closure (Ioo x y) := by
    rw [closure_Ioo hxy.ne]
    exact ⟨le_rfl, hxy.le⟩
  exact ContinuousWithinAt.closure_le hclose continuousWithinAt_const
    ((hf x hx).mono (fun z hz => ⟨hx.1.trans hz.1.le, hz.2.le.trans hy.2⟩)) hyz

namespace intervalIntegral

theorem sub_le_integral_of_interior_bound {u f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ s t : ℝ, s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      u t - u s ≤ ∫ r in s..t, f r)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    u t - u s ≤ ∫ r in s..t, f r := by
  have hint (r : ℝ) (hr : r ∈ Icc a b) : IntervalIntegrable f volume a r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1 (hf.mono (Icc_subset_Icc_right hr.2))
  have hH : ContinuousOn (fun r => ∫ z in a..r, f z) (Icc a b) := by
    simpa only [uIcc_of_le hab.le] using
      continuousOn_primitive_interval' (hint b ⟨hab.le, le_rfl⟩) left_mem_uIcc
  have hanti : AntitoneOn (fun r => u r - ∫ z in a..r, f z) (Ioo a b) := by
    intro x hx y hy hxy
    have h := hbound x y hx hy hxy
    have hi := integral_interval_sub_left
      (hint y (Ioo_subset_Icc_self hy)) (hint x (Ioo_subset_Icc_self hx))
    dsimp only
    linarith
  have h := (hu.sub hH).antitoneOn_Icc_of_antitoneOn_Ioo hanti hs ht hst
  have hi := integral_interval_sub_left (hint t ht) (hint s hs)
  change u t - (∫ z in a..t, f z) ≤ u s - (∫ z in a..s, f z) at h
  linarith

end intervalIntegral

namespace Poincare.Parabolic

theorem le_mul_exp_of_hasDerivAt_le_mul {f f' : ℝ → ℝ} {K a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t ≤ K * f t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (K * (t - s)) := by
  let g : ℝ → ℝ := fun r => f r * Real.exp (-K * (r - s))
  have hg : ContinuousOn g (Icc a b) := hf.mul (by fun_prop)
  have hd (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt g ((f' r - K * f r) * Real.exp (-K * (r - s))) r := by
    have he := (((hasDerivAt_id r).sub_const s).const_mul (-K)).exp
    convert! (hderiv r hr).mul he using 1
    dsimp only [g, id_eq]
    ring
  have ha : AntitoneOn g (Icc a b) := antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Icc a b) hg
    (fun r hr => (hd r (by simpa only [interior_Icc] using hr)).hasDerivWithinAt)
    (fun r hr => mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hbound r (by simpa only [interior_Icc] using hr))) (Real.exp_pos _).le)
  have h := ha hs ht hst
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (K * (t - s))).le
  simpa only [g, sub_self, mul_zero, Real.exp_zero, mul_one, mul_assoc,
    ← Real.exp_add, neg_mul, neg_add_cancel, neg_zero, zero_add] using hmul

theorem le_mul_exp_of_sub_le_integral_mul {f : ℝ → ℝ} {K a b : ℝ}
    (hK : 0 ≤ K) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ s t : ℝ, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      f t - f s ≤ ∫ r in s..t, K * f r)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (K * (t - s)) := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hforcing : ContinuousOn (fun r => K * f r) (Icc s t) :=
    continuousOn_const.mul (hf.mono hsub)
  have hint (r : ℝ) (hr : r ∈ Icc s t) :
      IntervalIntegrable (fun r => K * f r) volume s r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      (hforcing.mono (Icc_subset_Icc_right hr.2))
  let V : ℝ → ℝ := fun r => f s + ∫ z in s..r, K * f z
  have hV : ContinuousOn V (Icc s t) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le hst] using
      intervalIntegral.continuousOn_primitive_interval' (hint t ⟨hst, le_rfl⟩) left_mem_uIcc
  have hle (r : ℝ) (hr : r ∈ Icc s t) : f r ≤ V r := by
    have h := hbound s r hs (hsub hr) hr.1
    dsimp only [V]
    linarith
  have hd (r : ℝ) (hr : r ∈ Ioo s t) : HasDerivAt V (K * f r) r := by
    exact (intervalIntegral.integral_hasDerivAt_right (hint r (Ioo_subset_Icc_self hr))
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hforcing.mono Ioo_subset_Icc_self) r hr)
      (hforcing.continuousAt (Icc_mem_nhds hr.1 hr.2))).const_add (f s)
  have h := le_mul_exp_of_hasDerivAt_le_mul hV hd
    (fun r hr => mul_le_mul_of_nonneg_left (hle r (Ioo_subset_Icc_self hr)) hK)
    (show s ∈ Icc s t from ⟨le_rfl, hst⟩) (show t ∈ Icc s t from ⟨hst, le_rfl⟩) hst
  exact (hle t ⟨hst, le_rfl⟩).trans
    (by simpa only [V, intervalIntegral.integral_same, add_zero] using h)

theorem integral_le_mul_exp_of_energy_bound {f f' E : ℝ → ℝ} {K a b : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hf : ContinuousOn f (Icc a b))
    (hE : ContinuousOn E (Icc a b))
    (hderiv : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Ioo a b, f' t + E t ≤ K * f t)
    (hEnonneg : ∀ t ∈ Icc a b, 0 ≤ E t) (hfb : 0 ≤ f b) :
    (∫ t in a..b, E t) ≤ f a * Real.exp (K * (b - a)) := by
  let B : ℝ → ℝ := fun r => f a * Real.exp (K * (r - a))
  have hL (r : ℝ) (hr : r ∈ Icc a b) : f r ≤ B r :=
    le_mul_exp_of_hasDerivAt_le_mul hf hderiv
      (fun s hs => by linarith [hbound s hs, hEnonneg s (Ioo_subset_Icc_self hs)])
      ⟨le_rfl, hab⟩ hr hr.1
  have hint (r : ℝ) (hr : r ∈ Icc a b) : IntervalIntegrable E volume a r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1 (hE.mono (Icc_subset_Icc_right hr.2))
  have hprim : ContinuousOn (fun r => ∫ z in a..r, E z) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' (hint b ⟨hab, le_rfl⟩) left_mem_uIcc
  have hB (r : ℝ) : HasDerivAt B (K * B r) r := by
    convert! ((((hasDerivAt_id r).sub_const a).const_mul K).exp).const_mul (f a) using 1
    dsimp only [B, id_eq]
    ring
  let G : ℝ → ℝ := fun r => f r + (∫ z in a..r, E z) - B r
  have hG : ContinuousOn G (Icc a b) := (hf.add hprim).sub (by dsimp only [B]; fun_prop)
  have hd (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt G (f' r + E r - K * B r) r := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hint r (Ioo_subset_Icc_self hr))
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        (hE.mono Ioo_subset_Icc_self) r hr)
      (hE.continuousAt (Icc_mem_nhds hr.1 hr.2))
    exact ((hderiv r hr).add hi).sub (hB r)
  have ha : AntitoneOn G (Icc a b) := antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Icc a b) hG
    (fun r hr => (hd r (by simpa only [interior_Icc] using hr)).hasDerivWithinAt)
    (by
      intro r hr
      have hr' : r ∈ Ioo a b := by simpa only [interior_Icc] using hr
      have h := mul_le_mul_of_nonneg_left (hL r (Ioo_subset_Icc_self hr')) hK
      linarith [hbound r hr'])
  have h := ha (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
    (show b ∈ Icc a b from ⟨hab, le_rfl⟩) hab
  simp only [G, B, intervalIntegral.integral_same, add_zero, sub_self, mul_zero,
    Real.exp_zero, mul_one] at h
  linarith

end Poincare.Parabolic

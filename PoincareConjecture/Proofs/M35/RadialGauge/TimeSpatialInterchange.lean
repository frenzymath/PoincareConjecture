import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
private theorem interval_source_hasFDerivAt
    {H : ℝ → E → F} {a b t C : ℝ} (ht : t ∈ Icc a b)
    (hc : ∀ x, ContinuousOn (fun s => H s x) (Icc a b))
    (hdc : ∀ x, ContinuousOn (fun s => fderiv ℝ (H s) x) (Icc a b))
    (hs : ∀ s ∈ Icc a b, Differentiable ℝ (H s))
    (hb : ∀ s ∈ Icc a b, ∀ x, ‖fderiv ℝ (H s) x‖ ≤ C) (x : E) :
    HasFDerivAt (fun y => ∫ s in a..t, H s y)
      (∫ s in a..t, fderiv ℝ (H s) x) x := by
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc le_rfl ht.2
  have hsub' : uIoc a t ⊆ Icc a b := uIoc_subset_uIcc.trans hsub
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := univ) (F' := fun y s => fderiv ℝ (H s) y)
    (bound := fun _ => C) (by simp)
  · exact Eventually.of_forall (fun y =>
      ((hc y).mono hsub').aestronglyMeasurable measurableSet_uIoc)
  · exact ((hc x).mono hsub).intervalIntegrable
  · exact ((hdc x).mono hsub').aestronglyMeasurable measurableSet_uIoc
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs' y _
    exact hb s (hsub' hs') y
  · exact intervalIntegrable_const
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs' y _
    exact (hs s (hsub' hs') y).hasFDerivAt

private theorem time_fderiv_interchange_on_closed_interval
    {u H : ℝ → E → F} {a b t C : ℝ} (ht : t ∈ Ioo a b)
    (hu : ∀ s ∈ Icc a b, Differentiable ℝ (u s))
    (hPDE : ∀ s ∈ Icc a b, ∀ x, HasDerivAt (fun q => u q x) (H s x) s)
    (hc : ∀ x, ContinuousOn (fun s => H s x) (Icc a b))
    (hdc : ∀ x, ContinuousOn (fun s => fderiv ℝ (H s) x) (Icc a b))
    (hs : ∀ s ∈ Icc a b, Differentiable ℝ (H s))
    (hb : ∀ s ∈ Icc a b, ∀ x, ‖fderiv ℝ (H s) x‖ ≤ C) (x : E) :
    HasDerivAt (fun s => fderiv ℝ (u s) x) (fderiv ℝ (H t) x) t := by
  have hab : a ≤ b := ht.1.le.trans ht.2.le
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have heq (s : ℝ) (hs' : s ∈ Icc a b) :
      (fun y => ∫ q in a..s, H q y) = fun y => u s y - u a y := by
    funext y
    have hsub : uIcc a s ⊆ Icc a b := by
      rw [uIcc_of_le hs'.1]
      exact Icc_subset_Icc le_rfl hs'.2
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun q hq => hPDE q (hsub hq) y) ((hc y).mono hsub).intervalIntegrable
  have hdeq (s : ℝ) (hs' : s ∈ Icc a b) :
      fderiv ℝ (u s) x = fderiv ℝ (u a) x + ∫ q in a..s, fderiv ℝ (H q) x := by
    have hi := interval_source_hasFDerivAt hs' hc hdc hs hb x
    rw [heq s hs'] at hi
    have hd := ((hu s hs' x).hasFDerivAt.sub (hu a ha x).hasFDerivAt).unique hi
    rw [← hd]
    abel
  have hsub : uIcc a t ⊆ Icc a b := by
    rw [uIcc_of_le ht.1.le]
    exact Icc_subset_Icc le_rfl ht.2.le
  have hdc' : ContinuousOn (fun s => fderiv ℝ (H s) x) (Ioo a b) :=
    (hdc x).mono Ioo_subset_Icc_self
  have hi := intervalIntegral.integral_hasDerivAt_right
    ((hdc x).mono hsub).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hdc' t ht)
    (hdc'.continuousAt (isOpen_Ioo.mem_nhds ht))
  apply (hi.const_add (fderiv ℝ (u a) x)).congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs'
  exact hdeq s hs'



theorem time_fderiv_interchange
    {u H : ℝ → E → F} {a b t C : ℝ} (ht : t ∈ Ioo a b)
    (hu : ∀ s ∈ Ioo a b, Differentiable ℝ (u s))
    (hPDE : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun q => u q x) (H s x) s)
    (hc : ∀ x, ContinuousOn (fun s => H s x) (Ioo a b))
    (hdc : ∀ x, ContinuousOn (fun s => fderiv ℝ (H s) x) (Ioo a b))
    (hs : ∀ s ∈ Ioo a b, Differentiable ℝ (H s))
    (hb : ∀ s ∈ Ioo a b, ∀ x, ‖fderiv ℝ (H s) x‖ ≤ C) (x : E) :
    HasDerivAt (fun s => fderiv ℝ (u s) x) (fderiv ℝ (H t) x) t := by
  let l := (a + t) / 2
  let r := (t + b) / 2
  have hsub : Icc l r ⊆ Ioo a b := by
    intro s hs'
    dsimp only [l, r] at hs'
    constructor <;> linarith only [ht.1, ht.2, hs'.1, hs'.2]
  have hmem : t ∈ Ioo l r := by
    dsimp only [l, r]
    constructor <;> linarith [ht.1, ht.2]
  exact time_fderiv_interchange_on_closed_interval hmem
    (fun s hs' => hu s (hsub hs')) (fun s hs' => hPDE s (hsub hs'))
    (fun y => (hc y).mono hsub) (fun y => (hdc y).mono hsub)
    (fun s hs' => hs s (hsub hs')) (fun s hs' => hb s (hsub hs')) x

end PoincareConjecture.M35.RadialGauge

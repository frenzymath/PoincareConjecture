import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CrossRayRegion
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcLoop





noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareConjecture





theorem m64Intrinsic_exists_three_arc_loop
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T : Bool → ℝ) {S : ℝ} (hg : ∀ e, ContinuousOn (gamma e) (Icc 0 (T e)))
    (hs : ContinuousOn sigma (Icc 0 S)) (hT : ∀ e, 0 < T e) (hS : 0 < S)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e))) (hsi : InjOn sigma (Icc 0 S))
    (hstart : sigma 0 = gamma false 0) (hend : sigma S = gamma true (T true))
    (hjoin : gamma false (T false) = gamma true 0)
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S) :
    ∃ loop : ℝ → AnnulusCoordinates,
      ContinuousOn loop (Icc 0 2) ∧ loop 0 = loop 2 ∧ InjOn loop (Ico 0 2) ∧
      loop '' Icc 0 2 = gamma false '' Icc 0 (T false) ∪
        gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S := by
  let f (e : Bool) (x : ℝ) := gamma e (T e * x)
  have hparam (e : Bool) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
      T e * x ∈ Icc 0 (T e) :=
    ⟨mul_nonneg (hT e).le hx.1, by nlinarith [hT e, hx.2]⟩
  have hf (e : Bool) : ContinuousOn (f e) (Icc 0 1) :=
    (hg e).comp (continuous_const.mul continuous_id).continuousOn (fun _ hx => hparam e hx)
  have hfi (e : Bool) : InjOn (f e) (Icc 0 1) := by
    intro x hx y hy he
    exact mul_left_cancel₀ (hT e).ne' (hinj e (hparam e hx) (hparam e hy) he)
  have hfjoin : f false 1 = f true 0 := by
    simpa only [f, mul_one, mul_zero] using hjoin
  have hfmeet : ∀ x ∈ Icc 0 1, ∀ y ∈ Icc 0 1,
      f false x = f true y → x = 1 ∧ y = 0 := by
    intro x hx y hy he
    have hh := hab _ (hparam false hx) _ (hparam true hy) he
    constructor
    · nlinarith [hh.1, hT false]
    · exact (mul_eq_zero.mp hh.2).resolve_left (hT true).ne'
  obtain ⟨q, hq, hqi, hq0, hq1, hqimage⟩ :=
    m64Intrinsic_exists_embedded_join (hf false) (hf true) (hfi false) (hfi true)
      hfjoin hfmeet
  have hfimage (e : Bool) : f e '' Icc 0 1 = gamma e '' Icc 0 (T e) := by
    change (gamma e ∘ fun x => T e * x) '' Icc 0 1 = _
    rw [image_comp, image_mul_left_Icc' (hT e)]
    simp only [mul_zero, mul_one]
  rw [hfimage false, hfimage true] at hqimage
  have hq0' : q 0 = gamma false 0 := by simpa only [f, mul_zero] using hq0
  have hq1' : q 1 = gamma true (T true) := by simpa only [f, mul_one] using hq1
  have hqs : ∀ x ∈ Icc 0 1, ∀ y ∈ Icc 0 S,
      q x = sigma y → (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = S) := by
    intro x hx y hy he
    have hximage : q x ∈ gamma false '' Icc 0 (T false) ∪
        gamma true '' Icc 0 (T true) := hqimage ▸ mem_image_of_mem q hx
    rcases hximage with ⟨t, ht, htq⟩ | ⟨t, ht, htq⟩
    · obtain ⟨ht0, hy0⟩ := has t ht y hy (htq.trans he)
      refine Or.inl ⟨hqi hx (by norm_num) ?_, hy0⟩
      exact htq.symm.trans ((congrArg (gamma false) ht0).trans hq0'.symm)
    · obtain ⟨htT, hyS⟩ := hbs t ht y hy (htq.trans he)
      refine Or.inr ⟨hqi hx (by norm_num) ?_, hyS⟩
      exact htq.symm.trans ((congrArg (gamma true) htT).trans hq1'.symm)
  obtain ⟨loop, hl, he, hi, himage⟩ := m64Intrinsic_exists_simple_loop_between_arcs
    (by norm_num : (0 : ℝ) < 1) hS hq hs hqi hsi
    (hq0'.trans hstart.symm) (hq1'.trans hend.symm) hqs
  exact ⟨loop, hl, he, hi, by rwa [hqimage] at himage⟩

end PoincareConjecture

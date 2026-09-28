import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring









set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem exists_nonnested_reference_end_axis
    (ell gap lambda : ℝ) (hlambda : 0 < lambda) (hgap : lambda < gap) :
    ∃ g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      (∀ t : ℝ, g t = ell + lambda * t - (gap - lambda) *
        (1 - Real.smoothTransition (2 * t + 3 / 2))) ∧
      (∀ t : ℝ, lambda ≤ deriv (fun s : ℝ => g s) t) ∧
      StrictMono g ∧
      (∀ t : ℝ, t ≤ -3 / 4 → g t = ell - gap + lambda * (t + 1)) ∧
      (∀ t : ℝ, -1 / 4 ≤ t → g t = ell + lambda * t) ∧
      g (-1) = ell - gap ∧ g 0 = ell := by
  classical
  let chi : ℝ → ℝ := fun t => Real.smoothTransition (2 * t + 3 / 2)
  have hchi : ContDiff ℝ ∞ chi := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hchim : Monotone chi := by
    intro a b hab
    exact Real.smoothTransition.monotone (by linarith)
  have hchi0 (t : ℝ) (ht : t ≤ -3 / 4) : chi t = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    linarith
  have hchi1 (t : ℝ) (ht : -1 / 4 ≤ t) : chi t = 1 := by
    apply Real.smoothTransition.one_of_one_le
    linarith
  let f : ℝ → ℝ := fun t => ell + lambda * t - (gap - lambda) * (1 - chi t)
  have hf : ContDiff ℝ ∞ f :=
    (contDiff_const.add (contDiff_const.mul contDiff_id)).sub
      (contDiff_const.mul (contDiff_const.sub hchi))
  have hfd (t : ℝ) : HasDerivAt f
      (lambda + (gap - lambda) * deriv chi t) t := by
    have hd := ((hchi.differentiable (by simp)) t).hasDerivAt
    convert! (((hasDerivAt_id t).const_mul lambda).const_add ell).sub
      ((hd.const_sub 1).const_mul (gap - lambda)) using 1
    ring
  have hflower (t : ℝ) : lambda ≤ deriv f t := by
    rw [(hfd t).deriv]
    exact le_add_of_nonneg_right (mul_nonneg (sub_pos.mpr hgap).le hchim.deriv_nonneg)
  have hfpos (t : ℝ) : 0 < deriv f t := hlambda.trans_le (hflower t)
  have hfm : StrictMono f := strictMono_of_deriv_pos hfpos
  have hleft (t : ℝ) (ht : t ≤ -3 / 4) :
      f t = ell - gap + lambda * (t + 1) := by
    simp only [f, hchi0 t ht, sub_zero, mul_one]
    ring
  have hright (t : ℝ) (ht : -1 / 4 ≤ t) : f t = ell + lambda * t := by
    simp only [f, hchi1 t ht, sub_self, mul_zero, sub_zero]
  have hfs : Surjective f := by
    intro w
    let a := min (-3 / 4 : ℝ) ((w - ell + gap - lambda) / lambda)
    let b := max (-1 / 4 : ℝ) ((w - ell) / lambda)
    have ha : a ≤ -3 / 4 := min_le_left _ _
    have hb : -1 / 4 ≤ b := le_max_left _ _
    have hab : a ≤ b := by linarith
    have hlo : f a ≤ w := by
      rw [hleft a ha]
      have hh := mul_le_mul_of_nonneg_left
        (min_le_right (-3 / 4 : ℝ) ((w - ell + gap - lambda) / lambda)) hlambda.le
      have heq : lambda * ((w - ell + gap - lambda) / lambda) =
          w - ell + gap - lambda := by field_simp [hlambda.ne']
      rw [heq] at hh
      change lambda * a ≤ w - ell + gap - lambda at hh
      nlinarith only [hh]
    have hhi : w ≤ f b := by
      rw [hright b hb]
      have hh := mul_le_mul_of_nonneg_left
        (le_max_right (-1 / 4 : ℝ) ((w - ell) / lambda)) hlambda.le
      have heq : lambda * ((w - ell) / lambda) = w - ell := by
        field_simp [hlambda.ne']
      rw [heq] at hh
      change w - ell ≤ lambda * b at hh
      linarith only [hh]
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab hf.continuous.continuousOn ⟨hlo, hhi⟩
    exact ⟨t, ht⟩
  have hfdiff : ∀ t ∈ (univ : Set ℝ), ∃ A : ℝ ≃L[ℝ] ℝ,
      HasFDerivAt f (A : ℝ →L[ℝ] ℝ) t := by
    intro t _
    let L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (deriv f t)
    have hLi : Injective L := by
      apply (injective_iff_map_eq_zero L).mpr
      intro x hx
      change x * deriv f t = 0 at hx
      exact (mul_eq_zero.mp hx).resolve_right (hfpos t).ne'
    have hLs : Surjective L := by
      intro y
      refine ⟨y / deriv f t, ?_⟩
      change y / deriv f t * deriv f t = y
      exact div_mul_cancel₀ _ (hfpos t).ne'
    obtain ⟨A, hA⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hLi, hLs⟩
    refine ⟨ContinuousLinearEquiv.ofUnit A, ?_⟩
    change HasFDerivAt f (A : ℝ →L[ℝ] ℝ) t
    rw [hA]
    exact (((hf.differentiable (by simp)) t).hasDerivAt).hasFDerivAt
  let e := smoothOpenChart f isOpen_univ hf.contDiffOn hfdiff hfm.injective.injOn
  have het : e.target = univ := by
    change f '' univ = univ
    exact image_univ_of_surjective hfs
  have hei : ContDiff ℝ ∞ e.symm := by
    apply contDiffOn_univ.mp
    rw [← het]
    exact smoothOpenChart_symm_contDiffOn f isOpen_univ hf.contDiffOn hfdiff hfm.injective.injOn
  let g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toEquiv := {
      toFun := e
      invFun := e.symm
      left_inv := fun t => e.left_inv (mem_univ t)
      right_inv := fun t => e.right_inv (by rw [het]; exact mem_univ t) }
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := hei.contMDiff }
  refine ⟨g, fun _ => rfl, ?_, hfm, hleft, hright, ?_, ?_⟩
  · intro t
    change lambda ≤ deriv f t
    exact hflower t
  · change f (-1) = ell - gap
    rw [hleft (-1) (by norm_num)]
    ring
  · change f 0 = ell
    rw [hright 0 (by norm_num)]
    ring

end PoincareConjecture.M25.Topology3D

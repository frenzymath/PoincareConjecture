import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerClass
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Order.IntermediateValue












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex
open scoped Topology

namespace PoincareConjecture

private def m65CircleComplex (z : LoopCircle) : Circle :=
  ⟨orthonormalBasisOneI.repr.symm z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [LinearIsometryEquiv.norm_map, z.property]⟩

private theorem m65CircleComplex_continuous : Continuous m65CircleComplex :=
  (orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val).subtype_mk _

private theorem m65CircleComplex_injective : Function.Injective m65CircleComplex := by
  intro z w h
  apply Subtype.ext
  exact orthonormalBasisOneI.repr.symm.injective (congrArg (fun x : Circle => (x : ℂ)) h)

private theorem m65CircleComplex_dist (z w : LoopCircle) :
    dist (m65CircleComplex z) (m65CircleComplex w) = dist z w := by
  change dist (orthonormalBasisOneI.repr.symm z) (orthonormalBasisOneI.repr.symm w) =
    dist (z : LoopPlane) (w : LoopPlane)
  rw [dist_eq_norm, dist_eq_norm]
  rw [← map_sub, LinearIsometryEquiv.norm_map]

private theorem m65Circle_slit {z p : Circle} (h : z ≠ p) :
    ((-z / p : Circle) : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg]
  refine ⟨?_, Circle.coe_ne_zero _⟩
  intro he
  have heq : -z / p = (-1 : Circle) := Circle.injective_arg
    (he.trans (by simp))
  have hdiv : z / p = 1 := neg_injective (by simpa only [neg_div] using heq)
  exact h (div_eq_one.mp hdiv)




def m65WeakCircleArg (p z : LoopCircle) : ℝ :=
  Complex.arg (-orthonormalBasisOneI.repr.symm z / orthonormalBasisOneI.repr.symm p)




theorem m65WeakCircleArg_continuousAt {p z : LoopCircle} (h : z ≠ p) :
    ContinuousAt (fun q : LoopCircle × LoopCircle => m65WeakCircleArg q.1 q.2) (p, z) := by
  have hc : Continuous (fun q : LoopCircle × LoopCircle =>
      ((-m65CircleComplex q.2 / m65CircleComplex q.1 : Circle) : ℂ)) := by
    exact continuous_subtype_val.comp
      ((m65CircleComplex_continuous.comp continuous_snd).neg.div'
        (m65CircleComplex_continuous.comp continuous_fst))
  exact ContinuousAt.comp (f := fun q : LoopCircle × LoopCircle =>
      ((-m65CircleComplex q.2 / m65CircleComplex q.1 : Circle) : ℂ)) (x := (p, z))
    (Complex.continuousAt_arg (m65Circle_slit (m65CircleComplex_injective.ne h))) hc.continuousAt

private theorem m65Circle_exp_dist (x y : ℝ) : dist (Circle.exp x) (Circle.exp y) ≤ |x - y| := by
  change dist (Complex.exp (x * I)) (Complex.exp (y * I)) ≤ |x - y|
  rw [dist_eq_norm]
  have he : Complex.exp (x * I) - Complex.exp (y * I) =
      Complex.exp (y * I) * (Complex.exp ((x - y) * I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm, Real.norm_eq_abs, Complex.ofReal_sub] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

private theorem m65Circle_arg_dist (z w : Circle) : dist z w ≤ |Complex.arg z - Complex.arg w| := by
  simpa only [Circle.exp_arg] using m65Circle_exp_dist (Complex.arg z) (Complex.arg w)

private theorem m65Circle_quotient_dist (p z w : Circle) :
    dist (-z / p) (-w / p) = dist z w := by
  change dist (-(z : ℂ) / (p : ℂ)) (-(w : ℂ) / (p : ℂ)) = dist (z : ℂ) (w : ℂ)
  rw [dist_eq_norm, dist_eq_norm]
  rw [← sub_div, norm_div, Circle.norm_coe, div_one, neg_sub_neg, norm_sub_rev]

private theorem m65Homeomorph_arc_dist
    (h : LoopCircle ≃ₜ LoopCircle) (s : ℝ → LoopCircle) {a b : ℝ} (hab : a ≤ b)
    (hs : ContinuousOn s (Icc a b)) (hsi : InjOn s (Icc a b))
    (p : LoopCircle) (hp : ∀ t ∈ Icc a b, s t ≠ p)
    {t u : ℝ} (ht : t ∈ Icc a b) (hu : u ∈ Icc a b) :
    dist (h (s t)) (h (s u)) ≤
      |m65WeakCircleArg (h p) (h (s a)) - m65WeakCircleArg (h p) (h (s b))| := by
  let w (v : ℝ) : Circle := -m65CircleComplex (h (s v)) / m65CircleComplex (h p)
  let A (v : ℝ) := Complex.arg (w v)
  have hw : ContinuousOn w (Icc a b) :=
    (m65CircleComplex_continuous.comp_continuousOn
      (h.continuous.comp_continuousOn hs)).neg.div' continuousOn_const
  have hcoe : ContinuousOn (fun v => (w v : ℂ)) (Icc a b) :=
    continuous_subtype_val.comp_continuousOn hw
  have hA : ContinuousOn A (Icc a b) := by
    intro v hv
    exact ContinuousAt.comp_continuousWithinAt (f := fun v : ℝ => (w v : ℂ))
      (x := v) (s := Icc a b)
      (Complex.continuousAt_arg
        (m65Circle_slit (m65CircleComplex_injective.ne (h.injective.ne (hp v hv)))))
      (hcoe v hv)
  have hAi : InjOn A (Icc a b) := by
    intro x hx y hy he
    have hwxy : w x = w y := Circle.injective_arg he
    have hc : m65CircleComplex (h (s x)) = m65CircleComplex (h (s y)) :=
      neg_injective ((div_left_inj).mp hwxy)
    exact hsi hx hy (h.injective (m65CircleComplex_injective hc))
  have hmon := hA.strictMonoOn_of_injOn_Icc' hab hAi
  have harg : |A t - A u| ≤ |A a - A b| := by
    rcases hmon with hm | hm
    · have hta := hm.monotoneOn ⟨le_rfl, hab⟩ ht ht.1
      have htb := hm.monotoneOn ht ⟨hab, le_rfl⟩ ht.2
      have hua := hm.monotoneOn ⟨le_rfl, hab⟩ hu hu.1
      have hub := hm.monotoneOn hu ⟨hab, le_rfl⟩ hu.2
      rw [abs_sub_comm (A a), abs_of_nonneg (by linarith : 0 ≤ A b - A a)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · have hta := hm.antitoneOn ⟨le_rfl, hab⟩ ht ht.1
      have htb := hm.antitoneOn ht ⟨hab, le_rfl⟩ ht.2
      have hua := hm.antitoneOn ⟨le_rfl, hab⟩ hu hu.1
      have hub := hm.antitoneOn hu ⟨hab, le_rfl⟩ hu.2
      rw [abs_of_nonneg (by linarith : 0 ≤ A a - A b)]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have he : dist (w t) (w u) = dist (h (s t)) (h (s u)) :=
    (m65Circle_quotient_dist _ _ _).trans (m65CircleComplex_dist _ _)
  rw [← he]
  exact (m65Circle_arg_dist _ _).trans harg






theorem m65WeakCircleParameter_arc_dist
    (β : C(LoopCircle, LoopCircle)) (hβ : M65WeakCircleParameter β)
    (s : ℝ → LoopCircle) {a b : ℝ} (hab : a ≤ b)
    (hs : ContinuousOn s (Icc a b)) (hsi : InjOn s (Icc a b))
    (p : LoopCircle) (hp : ∀ t ∈ Icc a b, s t ≠ p)
    (ha : β (s a) ≠ β p) (hb : β (s b) ≠ β p)
    {t u : ℝ} (ht : t ∈ Icc a b) (hu : u ∈ Icc a b) :
    dist (β (s t)) (β (s u)) ≤
      |m65WeakCircleArg (β p) (β (s a)) - m65WeakCircleArg (β p) (β (s b))| := by
  let S := range (fun h : LoopCircle ≃ₜ LoopCircle =>
    (⟨h, h.continuous⟩ : C(LoopCircle, LoopCircle)))
  let l := 𝓝[S] β
  have : NeBot l := mem_closure_iff_nhdsWithin_neBot.mp hβ
  have heval (z : LoopCircle) :
      Tendsto (fun f : C(LoopCircle, LoopCircle) => f z) l (𝓝 (β z)) :=
    (continuous_eval_const z).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hleft := (heval (s t)).dist (heval (s u))
  have ha' := (m65WeakCircleArg_continuousAt ha).tendsto.comp
    ((heval p).prodMk_nhds (heval (s a)))
  have hb' := (m65WeakCircleArg_continuousAt hb).tendsto.comp
    ((heval p).prodMk_nhds (heval (s b)))
  apply le_of_tendsto_of_tendsto hleft ((ha'.sub hb').abs)
  filter_upwards [eventually_mem_nhdsWithin (a := β) (s := S)] with f hf
  obtain ⟨h, rfl⟩ := hf
  exact m65Homeomorph_arc_dist h s hab hs hsi p hp ht hu

end PoincareConjecture

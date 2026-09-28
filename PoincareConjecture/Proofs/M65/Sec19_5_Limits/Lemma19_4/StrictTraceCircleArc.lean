import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceCoordinates
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerCircleArc
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerConformalClass
import Mathlib.Analysis.Complex.RealDeriv










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65StrictTrace



def puncturedArc (p : LoopCircle) (t : ℝ) : LoopCircle :=
  ⟨orthonormalBasisOneI.repr
    (boundaryCoordinate (-orthonormalBasisOneI.repr.symm p) t), by
      rw [LinearIsometryEquiv.norm_map, norm_boundaryCoordinate]
      · simp
      · simp only [norm_neg, LinearIsometryEquiv.norm_map, p.property]⟩

private theorem puncturedArc_complex (p : LoopCircle) (t : ℝ) :
    orthonormalBasisOneI.repr.symm (puncturedArc p t : LoopPlane) =
      -orthonormalBasisOneI.repr.symm p * (Circle.exp t : ℂ) := by
  simp only [puncturedArc, LinearIsometryEquiv.symm_apply_apply,
    boundaryCoordinate, Circle.coe_exp, mul_comm Complex.I (t : ℂ)]



theorem puncturedArc_continuous (p : LoopCircle) : Continuous (puncturedArc p) :=
  (orthonormalBasisOneI.repr.continuous.comp
    ((contDiff_boundaryCoordinate _).continuous.comp Complex.continuous_ofReal)).subtype_mk _



theorem puncturedArc_arg (p z : LoopCircle) :
    puncturedArc p (m65WeakCircleArg p z) = z := by
  apply Subtype.ext
  apply orthonormalBasisOneI.repr.symm.injective
  rw [puncturedArc_complex]
  have hp : ‖orthonormalBasisOneI.repr.symm (p : LoopPlane)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, p.property]
  have hz : ‖orthonormalBasisOneI.repr.symm (z : LoopPlane)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, z.property]
  have hn : ‖-orthonormalBasisOneI.repr.symm (z : LoopPlane) /
      orthonormalBasisOneI.repr.symm (p : LoopPlane)‖ = 1 := by
    rw [norm_div, norm_neg, hz, hp, div_one]
  have he := norm_mul_exp_arg_mul_I
    (-orthonormalBasisOneI.repr.symm (z : LoopPlane) /
      orthonormalBasisOneI.repr.symm (p : LoopPlane))
  rw [hn, Complex.ofReal_one, one_mul] at he
  change -orthonormalBasisOneI.repr.symm (p : LoopPlane) *
    Complex.exp (↑(m65WeakCircleArg p z) * Complex.I) = _
  rw [m65WeakCircleArg, he]
  have hp0 : orthonormalBasisOneI.repr.symm (p : LoopPlane) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hp]; norm_num)
  simp only [neg_div, neg_mul_neg]
  exact mul_div_cancel₀ _ hp0



theorem arg_puncturedArc (p : LoopCircle) {t : ℝ} (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    m65WeakCircleArg p (puncturedArc p t) = t := by
  have hp : orthonormalBasisOneI.repr.symm (p : LoopPlane) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [LinearIsometryEquiv.norm_map, p.property]
    norm_num
  rw [m65WeakCircleArg, puncturedArc_complex]
  have he : -(-orthonormalBasisOneI.repr.symm (p : LoopPlane) * (Circle.exp t : ℂ)) /
      orthonormalBasisOneI.repr.symm (p : LoopPlane) = (Circle.exp t : ℂ) := by
    field_simp
  rw [he]
  exact Circle.arg_exp ht.1 ht.2.le



theorem weakCircleArg_mem {p z : LoopCircle} (hz : z ≠ p) :
    m65WeakCircleArg p z ∈ Ioo (-Real.pi) Real.pi := by
  refine ⟨neg_pi_lt_arg _, lt_of_le_of_ne (arg_le_pi _) ?_⟩
  intro he
  apply hz
  rw [← puncturedArc_arg p z, he]
  apply Subtype.ext
  apply orthonormalBasisOneI.repr.symm.injective
  rw [puncturedArc_complex, Circle.coe_exp, Complex.exp_pi_mul_I]
  simp



theorem puncturedArc_hasDerivAt (p : LoopCircle) (t : ℝ) :
    ∃ v : LoopPlane, v ≠ 0 ∧
      HasDerivAt (fun s : ℝ => (puncturedArc p s : LoopPlane)) v t := by
  refine ⟨orthonormalBasisOneI.repr
    (Complex.I * boundaryCoordinate (-orthonormalBasisOneI.repr.symm p) t), ?_, ?_⟩
  · intro h
    have hp : -orthonormalBasisOneI.repr.symm (p : LoopPlane) ≠ 0 := by
      apply norm_ne_zero_iff.mp
      rw [norm_neg, LinearIsometryEquiv.norm_map, p.property]
      norm_num
    have hz := orthonormalBasisOneI.repr.injective (h.trans (map_zero _).symm)
    exact mul_ne_zero Complex.I_ne_zero (mul_ne_zero hp (exp_ne_zero _)) hz
  · exact orthonormalBasisOneI.repr.toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_boundaryCoordinate _ (t : ℂ)).comp_ofReal




theorem exists_collapsed_arc (beta : C(LoopCircle, LoopCircle))
    (hbeta : M65WeakCircleParameter beta) (hnot : ¬Function.Injective beta) :
    ∃ (p : LoopCircle) (a b : ℝ), a < b ∧ Icc a b ⊆ Ioo (-Real.pi) Real.pi ∧
      InjOn (puncturedArc p) (Icc a b) ∧
      ∀ t ∈ Icc a b, beta (puncturedArc p t) = beta (puncturedArc p a) := by
  classical
  obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hnot
  let q : LoopCircle := ⟨-(beta x : LoopPlane), by simp only [norm_neg, (beta x).property]⟩
  have hq : q ≠ beta x := by
    intro h
    have he : -(beta x : LoopPlane) = (beta x : LoopPlane) := congrArg Subtype.val h
    have hz : (beta x : LoopPlane) = 0 := by
      ext i
      have hi := congrArg (fun v : LoopPlane => v i) he
      change -(beta x : LoopPlane) i = (beta x : LoopPlane) i at hi
      change (beta x : LoopPlane) i = 0
      linarith
    have hn := (beta x).property
    rw [hz, norm_zero] at hn
    norm_num at hn
  obtain ⟨p, hp⟩ := hbeta.surjective q
  have hx : x ≠ p := by intro h; apply hq; rw [← hp, ← h]
  have hy : y ≠ p := by intro h; apply hq; rw [← hp, ← h, ← hxy]
  let u := m65WeakCircleArg p x
  let v := m65WeakCircleArg p y
  have hu := weakCircleArg_mem hx
  have hv := weakCircleArg_mem hy
  have huv : u ≠ v := by
    intro h
    apply hne
    rw [← puncturedArc_arg p x, ← puncturedArc_arg p y]
    exact congrArg (puncturedArc p) h
  let a := min u v
  let b := max u v
  have hab : a < b := min_lt_max.mpr huv
  have hI : Icc a b ⊆ Ioo (-Real.pi) Real.pi := by
    intro t ht
    exact ⟨lt_of_lt_of_le (lt_min hu.1 hv.1) ht.1,
      lt_of_le_of_lt ht.2 (max_lt hu.2 hv.2)⟩
  have hsi : InjOn (puncturedArc p) (Icc a b) := by
    intro s hs t ht he
    simpa only [arg_puncturedArc p (hI hs), arg_puncturedArc p (hI ht)] using
      congrArg (m65WeakCircleArg p) he
  have hav : beta (puncturedArc p a) = beta x := by
    rcases le_total u v with h | h
    · rw [show a = u from min_eq_left h, puncturedArc_arg]
    · rw [show a = v from min_eq_right h, puncturedArc_arg, ← hxy]
  have hbval : beta (puncturedArc p b) = beta x := by
    rcases le_total u v with h | h
    · rw [show b = v from max_eq_right h, puncturedArc_arg, ← hxy]
    · rw [show b = u from max_eq_left h, puncturedArc_arg]
  have hsep : beta x ≠ beta p := by rw [hp]; exact hq.symm
  refine ⟨p, a, b, hab, hI, hsi, ?_⟩
  intro t ht
  have hd := m65WeakCircleParameter_arc_dist beta hbeta (puncturedArc p) hab.le
    (puncturedArc_continuous p).continuousOn hsi p (fun s hs he => by
      have ha := arg_puncturedArc p (hI hs)
      have hpp : m65WeakCircleArg p p = Real.pi := by
        have hp0 : orthonormalBasisOneI.repr.symm (p : LoopPlane) ≠ 0 := by
          apply norm_ne_zero_iff.mp
          rw [LinearIsometryEquiv.norm_map, p.property]
          norm_num
        change Complex.arg (-orthonormalBasisOneI.repr.symm (p : LoopPlane) /
          orthonormalBasisOneI.repr.symm (p : LoopPlane)) = Real.pi
        rw [neg_div, div_self hp0, Complex.arg_neg_one]
      rw [he, hpp] at ha
      exact (hI hs).2.ne ha.symm)
    (hav ▸ hsep) (hbval ▸ hsep) ht (left_mem_Icc.mpr hab.le)
  rw [hav, hbval, sub_self, abs_zero] at hd
  rw [hav]
  exact dist_le_zero.mp hd

end PoincareConjecture.M65StrictTrace

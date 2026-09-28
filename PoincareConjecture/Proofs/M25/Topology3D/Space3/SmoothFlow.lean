import PoincareConjecture.Proofs.M25.Topology3D.Space3.LocalFlowRegularity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactField
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false

open Set
open scoped ContDiff NNReal Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (f : E → E) {K L : ℝ≥0}
variable (hK : LipschitzWith K f) (hL : ∀ x, ‖f x‖ ≤ L)

theorem boundedFlow_smooth_multiple {d : ℝ}
    (hstrip : ContDiffOn ℝ ∞ (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2)
      (univ ×ˢ Ioo (-d) d)) (n : ℕ) (p : E × ℝ) (hp : p.2 ∈ Ioo (-d) d) :
    ContDiffAt ℝ ∞ (fun q : E × ℝ => boundedFlow f hK hL q.1 ((n : ℝ) * q.2)) p := by
  induction n with
  | zero => simpa only [Nat.cast_zero, zero_mul, boundedFlow_zero] using contDiffAt_fst
  | succ n ih =>
    have houter : ContDiffAt ℝ ∞
        (fun q : E × ℝ => boundedFlow f hK hL q.1 q.2)
        (boundedFlow f hK hL p.1 ((n : ℝ) * p.2), p.2) :=
      hstrip.contDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp⟩)
    have hcomp := houter.comp p (ih.prodMk contDiffAt_snd)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      boundedFlow_add] using hcomp

theorem boundedFlow_contDiff_of_smooth_strip {d : ℝ} (hd : 0 < d)
    (hstrip : ContDiffOn ℝ ∞ (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2)
      (univ ×ˢ Ioo (-d) d)) :
    ContDiff ℝ ∞ (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨n, hn⟩ := exists_nat_gt (|p.2| / d)
  have hn0 : 0 < (n : ℝ) := (div_nonneg (abs_nonneg p.2) hd.le).trans_lt hn
  have hsmall : p.2 / (n : ℝ) ∈ Ioo (-d) d := by
    apply abs_lt.mp
    rw [abs_div, abs_of_pos hn0, div_lt_iff₀ hn0]
    have hbound := (div_lt_iff₀ hd).mp hn
    nlinarith
  have hmulti := boundedFlow_smooth_multiple f hK hL hstrip n (p.1, p.2 / n) hsmall
  have hcomp := hmulti.comp p (contDiffAt_fst.prodMk (contDiffAt_snd.div_const (n : ℝ)))
  have hscale (q : E × ℝ) : (n : ℝ) * (q.2 / n) = q.2 := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ q.2 hn0.ne']
  simpa only [Function.comp_def, hscale] using hcomp

theorem boundedFlow_contDiff (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun p : E × ℝ => boundedFlow f hK hL p.1 p.2) := by
  obtain ⟨d, hd, hstrip⟩ := boundedFlow_smooth_strip f hK hL hf hs
  exact boundedFlow_contDiff_of_smooth_strip f hK hL hd hstrip

noncomputable def boundedFlowDiffeomorph (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (t : ℝ) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toEquiv := boundedFlowEquiv f hK hL t
  contMDiff_toFun :=
    ((boundedFlow_contDiff f hK hL hf hs).comp
      (contDiff_id.prodMk contDiff_const)).contMDiff
  contMDiff_invFun :=
    ((boundedFlow_contDiff f hK hL hf hs).comp
      (contDiff_id.prodMk contDiff_const)).contMDiff

end PoincareConjecture.M25.Topology3D

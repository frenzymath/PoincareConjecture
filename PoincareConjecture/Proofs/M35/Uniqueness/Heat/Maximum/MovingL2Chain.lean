import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

theorem moving_hilbert_entropy_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (E : ℝ → H → ℝ) (U G : ℝ → H) {t d : ℝ} {v : H}
    (hU : HasDerivAt U v t) (hG : ContinuousAt G t)
    (hfixed : HasDerivAt (fun s => E s (U t)) d t)
    {C : ℝ} (hR : ∀ᶠ s in 𝓝 t,
      ‖E s (U s) - E s (U t) - inner ℝ (G s) (U s - U t)‖ ≤
        C * ‖U s - U t‖ ^ 2) :
    HasDerivAt (fun s => E s (U s)) (d + inner ℝ (G t) v) t := by
  let R (s : ℝ) := E s (U s) - E s (U t) - inner ℝ (G t) (U s - U t)
  have hsmall : (fun s => ‖U s - U t‖) =o[𝓝 t] (fun _ => (1 : ℝ)) :=
    ((isLittleO_one_iff ℝ).mpr (by
      simpa only [sub_self] using
        (hU.continuousAt.tendsto.sub (tendsto_const_nhds (x := U t))))).norm_left
  have hbig : (fun s => ‖U s - U t‖) =O[𝓝 t] (fun s => s - t) :=
    hU.isBigO_sub.norm_left
  have hquad : (fun s => ‖U s - U t‖ ^ 2) =o[𝓝 t] (fun s => s - t) := by
    simpa only [pow_two, one_mul] using hsmall.mul_isBigO hbig
  have hgsmall : (fun s => ‖G s - G t‖) =o[𝓝 t] (fun _ => (1 : ℝ)) :=
    ((isLittleO_one_iff ℝ).mpr (by
      simpa only [sub_self] using
        (hG.tendsto.sub (tendsto_const_nhds (x := G t))))).norm_left
  have hcross : (fun s => ‖G s - G t‖ * ‖U s - U t‖) =o[𝓝 t] (fun s => s - t) := by
    simpa only [one_mul] using hgsmall.mul_isBigO hbig
  have hb : R =O[𝓝 t] (fun s => C * ‖U s - U t‖ ^ 2 +
      ‖G s - G t‖ * ‖U s - U t‖) := by
    apply IsBigO.of_bound 1
    filter_upwards [hR] with s hs
    have he : R s = (E s (U s) - E s (U t) - inner ℝ (G s) (U s - U t)) +
        inner ℝ (G s - G t) (U s - U t) := by
      rw [inner_sub_left]
      dsimp only [R]
      ring
    rw [he, one_mul]
    exact ((norm_add_le _ _).trans (add_le_add hs (norm_inner_le_norm _ _))).trans
      (le_abs_self _)
  have hr : R =o[𝓝 t] (fun s => s - t) :=
    hb.trans_isLittleO ((hquad.const_mul_left C).add hcross)
  have hr0 : R t = 0 := by simp [R]
  have hrd : HasDerivAt R 0 t := by
    rw [hasDerivAt_iff_isLittleO]
    simpa only [hr0, sub_zero, mul_zero, smul_zero] using hr
  have hlin := ((innerSL ℝ (G t)).hasFDerivAt.comp_hasDerivAt t (hU.sub_const (U t)))
  have hd : HasDerivAt (fun s => E s (U t) + inner ℝ (G t) (U s - U t) + R s)
      (d + inner ℝ (G t) v + 0) t := (hfixed.add hlin).add hrd
  convert! hd using 1
  · funext s
    simp only [R]
    ring
  · simp only [add_zero]

end PoincareConjecture.M35.Uniqueness.Heat

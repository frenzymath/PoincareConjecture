import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Coordinates
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff

namespace Poincare.Topology.Plane.Curves

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem graph_transverse_ne_zero
    (A B : E ≃L[ℝ] (ℝ × ℝ)) {v d : E} {r s f' g' : ℝ}
    (hs : s ≠ 0) (hAv : A v = r • ((1 : ℝ), f'))
    (hBv : B v = s • ((1 : ℝ), g'))
    (hAd : (A d).2 - f' * (A d).1 ≠ 0) :
    (B d).2 - g' * (B d).1 ≠ 0 := by
  intro hzero
  let c := (B d).1 / s
  have hdc : d = c • v := by
    apply B.injective
    rw [map_smul, hBv, smul_smul]
    have hcs : c * s = (B d).1 := by dsimp [c]; exact div_mul_cancel₀ _ hs
    rw [hcs]
    apply Prod.ext
    · simp
    · change (B d).2 = (B d).1 * g'
      linarith
  apply hAd
  rw [hdc, map_smul, hAv, smul_smul]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one]
  ring

theorem graph_transverse_pos_of_eventually_above
    (A B : E ≃L[ℝ] (ℝ × ℝ)) {p v d : E} {r s f' : ℝ} {g : ℝ → ℝ}
    (hs : s ≠ 0) (hAv : A v = r • ((1 : ℝ), f'))
    (hBv : B v = s • ((1 : ℝ), deriv g (B p).1))
    (hAd : (A d).2 - f' * (A d).1 ≠ 0)
    (hg : DifferentiableAt ℝ g (B p).1) (hp : (B p).2 = g (B p).1)
    (hside : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < (B (p + t • d)).2 - g (B (p + t • d)).1) :
    0 < (B d).2 - deriv g (B p).1 * (B d).1 := by
  let f : ℝ → ℝ := fun t => (B (p + t • d)).2 - g (B (p + t • d)).1
  have hx : HasDerivAt (fun t : ℝ => (B (p + t • d)).1) (B d).1 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (B p).1).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (B d).1) using 1 <;>
      simp [map_add, map_smul, Pi.add_def]
  have hy : HasDerivAt (fun t : ℝ => (B (p + t • d)).2) (B d).2 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (B p).2).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (B d).2) using 1 <;>
      simp [map_add, map_smul, Pi.add_def]
  have hgc : HasDerivAt (fun t : ℝ => g (B (p + t • d)).1)
      (deriv g (B p).1 * (B d).1) 0 := by
    have hg' : HasDerivAt g (deriv g (B p).1) (B (p + (0 : ℝ) • d)).1 := by
      simpa only [zero_smul, add_zero] using hg.hasDerivAt
    exact hg'.comp 0 hx
  have hf : HasDerivAt f ((B d).2 - deriv g (B p).1 * (B d).1) 0 :=
    hy.sub hgc
  have hfzero : f 0 = 0 := by simp only [f, zero_smul, add_zero, hp, sub_self]
  have hnonneg : 0 ≤ (B d).2 - deriv g (B p).1 * (B d).1 := by
    apply ge_of_tendsto hf.tendsto_slope_zero_right
    filter_upwards [hside, self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    simpa only [zero_add, hfzero, sub_zero, smul_eq_mul] using
      mul_nonneg (inv_nonneg.mpr htpos'.le) ht.le
  exact lt_of_le_of_ne hnonneg (Ne.symm (graph_transverse_ne_zero A B hs hAv hBv hAd))

end Poincare.Topology.Plane.Curves

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.LinearAlgebra.AffineSpace.Ordered





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

namespace PoincareConjecture

private theorem eventually_gt_of_deriv_pos
    {f : ℝ → ℝ} {d a : ℝ} (hd : HasDerivAt f d a) (hpos : 0 < d) :
    ∀ᶠ t in 𝓝[>] a, f a < f t := by
  have hlim := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  filter_upwards [hlim.eventually (Ioi_mem_nhds hpos), self_mem_nhdsWithin] with t ht hat
  exact (slope_pos_iff hat).mp ht





theorem m64_radial_enters_positive_corner
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : E → X} {K : Set X} {phi : E → ℝ × ℝ} {J : E →L[ℝ] ℝ × ℝ}
    (hphi : HasFDerivAt phi J 0) (hzero : phi 0 = 0)
    (hcorner : ∀ᶠ z in 𝓝 (0 : E), 0 ≤ (phi z).1 ∧ 0 ≤ (phi z).2 → e z ∈ K)
    {w : E} (hw : 0 < (J w).1 ∧ 0 < (J w).2) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), e (t • w) ∈ K := by
  have hpath : HasDerivAt (fun t : ℝ => t • w) w 0 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const w
  have hd : HasDerivAt (fun t : ℝ => phi (t • w)) (J w) 0 := by
    have hd' : HasFDerivAt phi J ((0 : ℝ) • w) := by
      simpa only [zero_smul] using hphi
    exact hd'.comp_hasDerivAt 0 hpath
  have hd1 : HasDerivAt (fun t : ℝ => (phi (t • w)).1) (J w).1 0 := by
    convert! hasFDerivAt_fst.comp_hasDerivAt 0 hd using 1
  have hd2 : HasDerivAt (fun t : ℝ => (phi (t • w)).2) (J w).2 0 := by
    convert! hasFDerivAt_snd.comp_hasDerivAt 0 hd using 1
  have hside : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ (phi (t • w)).1 ∧ 0 ≤ (phi (t • w)).2 → e (t • w) ∈ K :=
    ((continuous_id.smul continuous_const).tendsto' 0 0 (zero_smul ℝ w)).eventually
      hcorner |>.filter_mono nhdsWithin_le_nhds
  filter_upwards [hside, eventually_gt_of_deriv_pos hd1 hw.1,
    eventually_gt_of_deriv_pos hd2 hw.2] with t ht h1 h2
  apply ht
  simpa only [zero_smul, hzero, Prod.fst_zero, Prod.snd_zero] using And.intro h1.le h2.le





theorem m64_radial_leaves_terminal_corner
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {e : E → X} {K : Set X} {f : E → ℝ} {L : E →L[ℝ] ℝ} {v : E}
    (hf : HasFDerivAt f L v) (hzero : f v = 0) (hneg : L v < 0)
    (hcorner : ∀ᶠ z in 𝓝 v, e z ∈ K → 0 ≤ f z) :
    ∀ᶠ a in 𝓝[>] (1 : ℝ), e (a • v) ∉ K := by
  have hpath : HasDerivAt (fun a : ℝ => a • v) v 1 := by
    simpa only [one_smul, id_eq] using (hasDerivAt_id (1 : ℝ)).smul_const v
  have hd : HasDerivAt (fun a : ℝ => f (a • v)) (L v) 1 := by
    have hd' : HasFDerivAt f L ((1 : ℝ) • v) := by
      simpa only [one_smul] using hf
    exact hd'.comp_hasDerivAt 1 hpath
  have hside : ∀ᶠ a in 𝓝[>] (1 : ℝ), e (a • v) ∈ K → 0 ≤ f (a • v) :=
    ((continuous_id.smul continuous_const).tendsto' 1 v (one_smul ℝ v)).eventually
      hcorner |>.filter_mono nhdsWithin_le_nhds
  filter_upwards [hside, eventually_gt_of_deriv_pos hd.neg (neg_pos.mpr hneg)] with a ha hneg'
  have hfneg : f (a • v) < 0 := by
    simpa only [Pi.neg_apply, one_smul, hzero, neg_zero, neg_pos] using hneg'
  exact fun hmem => hfneg.not_ge (ha hmem)

end PoincareConjecture

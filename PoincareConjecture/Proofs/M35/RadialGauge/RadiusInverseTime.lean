import PoincareConjecture.Proofs.M35.RadialGauge.RadiusInverseFamily

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

theorem mapRadiusInverse_hasDerivAt_time
    {w : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (Function.uncurry w) (J ×ˢ univ))
    (hs : ∀ t ∈ J, ContDiff ℝ ∞ (w t))
    (hv : ∀ t ∈ J, ∀ r, (1 + |r|) * |w t r| ≤ 1 / 8)
    (hd : ∀ t ∈ J, ∀ r, (1 + |r|) * |deriv (w t) r| ≤ 1 / 8)
    {t s v : ℝ} (ht : t ∈ J)
    (htime : HasDerivAt (fun a => mapRadius (w a) (mapRadiusInverse w t s)) v t) :
    HasDerivAt (fun a => mapRadiusInverse w a s)
      (-v / deriv (mapRadius (w t)) (mapRadiusInverse w t s)) t := by
  let q (a : ℝ) := mapRadiusInverse w a s
  let r := q t
  let S (z : ℝ × ℝ) := mapRadius (w z.1) z.2
  let L := fderiv ℝ S (t, r)
  let d := deriv (mapRadius (w t)) r
  have hq : DifferentiableAt ℝ q t :=
    ((mapRadiusInverse_contDiffAt hJ hc hs hv hd (p := (t, s)) ht).comp t
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
  have hSc : ContDiffOn ℝ 1 S (J ×ˢ univ) := contDiffOn_snd.mul hc.exp
  have hS : HasFDerivAt S L (t, r) :=
    ((hSc.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ r⟩)).differentiableAt
      (by norm_num)).hasFDerivAt
  have htime' : L (1, 0) = v := by
    have hleft := hS.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t r))
    change HasDerivAt (fun a => mapRadius (w a) (mapRadiusInverse w t s))
      (L (1, 0)) t at hleft
    exact hleft.unique htime
  have hspace : L (0, 1) = d := by
    have hleft := hS.comp_hasDerivAt r
      ((hasDerivAt_const r t).prodMk (hasDerivAt_id r))
    exact hleft.unique
      (((contDiff_id.mul (hs t ht).exp).differentiable (by simp) r).hasDerivAt)
  have hchain : HasDerivAt (fun a => S (a, q a)) (L (1, deriv q t)) t := by
    simpa only [Function.comp_def, id_eq] using
      hS.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hq.hasDerivAt)
  have hconstant : HasDerivAt (fun a => S (a, q a)) 0 t := by
    apply (hasDerivAt_const t s).congr_of_eventuallyEq
    filter_upwards [hJ.mem_nhds ht] with a ha
    exact (mapRadius_inverse_properties (hs a ha) (hv a ha) (hd a ha)).2.2.1 s
  have heq := hchain.unique hconstant
  have hlin : L (1, deriv q t) = v + deriv q t * d := by
    rw [show (1, deriv q t) = (1, 0) + deriv q t • ((0, 1) : ℝ × ℝ) by
      ext <;> simp]
    rw [map_add, map_smul, smul_eq_mul, htime', hspace]
  rw [hlin] at heq
  have hdpos : 0 < d := by
    have h := mapRadius_deriv_sub_one_bound (hs t ht) r (hv t ht r) (hd t ht r)
    dsimp only [d]
    linarith only [(abs_le.mp h).1]
  have hdq : deriv q t = -v / d := by
    apply (eq_div_iff hdpos.ne').mpr
    linarith only [heq]
  simpa only [hdq] using hq.hasDerivAt

theorem mapRadiusInverse_hasDerivAt_time_of_logarithm
    {w : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (Function.uncurry w) (J ×ˢ univ))
    (hs : ∀ t ∈ J, ContDiff ℝ ∞ (w t))
    (hv : ∀ t ∈ J, ∀ r, (1 + |r|) * |w t r| ≤ 1 / 8)
    (hd : ∀ t ∈ J, ∀ r, (1 + |r|) * |deriv (w t) r| ≤ 1 / 8)
    {t s v : ℝ} (ht : t ∈ J)
    (htime : HasDerivAt (fun a => w a (mapRadiusInverse w t s)) v t) :
    HasDerivAt (fun a => mapRadiusInverse w a s)
      (-(s * v) / deriv (mapRadius (w t)) (mapRadiusInverse w t s)) t := by
  have htρ := mapRadius_hasDerivAt_time (mapRadiusInverse w t s) htime
  have hinv := (mapRadius_inverse_properties (hs t ht) (hv t ht) (hd t ht)).2.2.1 s
  rw [hinv] at htρ
  exact mapRadiusInverse_hasDerivAt_time hJ hc hs hv hd ht htρ

end PoincareConjecture.M35.RadialGauge

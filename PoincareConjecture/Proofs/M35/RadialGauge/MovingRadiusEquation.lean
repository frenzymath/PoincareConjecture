import PoincareConjecture.Proofs.M35.RadialGauge.RadiusInverseFamily

set_option autoImplicit false

open Set
open scoped ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

theorem mapRadius_comp_hasDerivAt
    {w : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (Function.uncurry w) (J ×ˢ univ))
    {q : ℝ → ℝ} {t a b : ℝ} (ht : t ∈ J)
    (hs : ContDiff ℝ ∞ (w t))
    (hq : HasDerivAt q b t)
    (hw : HasDerivAt (fun s => mapRadius (w s) (q t)) a t) :
    HasDerivAt (fun s => mapRadius (w s) (q s))
      (a + b * deriv (mapRadius (w t)) (q t)) t := by
  let S (z : ℝ × ℝ) := mapRadius (w z.1) z.2
  let L := fderiv ℝ S (t, q t)
  have hSc : ContDiffOn ℝ 1 S (J ×ˢ univ) := contDiffOn_snd.mul hc.exp
  have hS : HasFDerivAt S L (t, q t) :=
    ((hSc.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ _⟩)).differentiableAt
      (by norm_num)).hasFDerivAt
  have htime : L (1, 0) = a := by
    have h := hS.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t (q t)))
    change HasDerivAt (fun s => mapRadius (w s) (q t)) (L (1, 0)) t at h
    exact h.unique hw
  have hspace : L (0, 1) = deriv (mapRadius (w t)) (q t) :=
    (hS.comp_hasDerivAt (q t) ((hasDerivAt_const (q t) t).prodMk (hasDerivAt_id (q t)))).unique
      (((contDiff_id.mul hs.exp).differentiable (by simp) (q t)).hasDerivAt)
  have h := hS.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hq)
  have hlin : L (1, b) = a + b * deriv (mapRadius (w t)) (q t) := by
    rw [show (1, b) = (1, 0) + b • ((0, 1) : ℝ × ℝ) by ext <;> simp,
      map_add, map_smul, smul_eq_mul, htime, hspace]
  simpa only [hlin, Function.comp_def, id_eq] using h

theorem corrected_radius_comp_solves_harmonic
    {w : ℝ → ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (Function.uncurry w) (J ×ˢ univ))
    {q f f₀ velocity : ℝ → ℝ} {t dimension : ℝ} (ht : t ∈ J)
    (hs : ContDiff ℝ ∞ (w t))
    (hq : HasDerivAt q (velocity (q t)) t)
    (hw : HasDerivAt (fun s => mapRadius (w s) (q t))
      (harmonicRadialOperator dimension f f₀ velocity (mapRadius (w t)) (q t)) t) :
    HasDerivAt (fun s => mapRadius (w s) (q s))
      (deriv (deriv (mapRadius (w t))) (q t) +
        (dimension - 1) * (deriv f (q t) / f (q t)) * deriv (mapRadius (w t)) (q t) -
        (dimension - 1) * f₀ (mapRadius (w t) (q t)) *
          deriv f₀ (mapRadius (w t) (q t)) / f (q t) ^ 2) t := by
  have h := mapRadius_comp_hasDerivAt hJ hc ht hs hq hw
  simpa only [harmonicRadialOperator, sub_add_cancel] using h

end PoincareConjecture.M35.RadialGauge

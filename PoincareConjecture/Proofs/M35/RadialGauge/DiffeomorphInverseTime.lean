import PoincareConjecture.Proofs.M35.RadialGauge.DiffeomorphFamilyInverse











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem diffeomorph_family_symm_hasDerivAt
    {Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) V V ∞} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (fun p : ℝ × V => Φ p.1 p.2) (J ×ˢ univ))
    {t : ℝ} {y v : V} (ht : t ∈ J)
    (htime : HasDerivAt (fun a => Φ a ((Φ t).symm y)) v t) :
    HasDerivAt (fun a => (Φ a).symm y)
      (-(fderiv ℝ ((Φ t).symm : V → V) y v)) t := by
  let q (a : ℝ) := (Φ a).symm y
  let r := q t
  let S (z : ℝ × V) := Φ z.1 z.2
  let L := fderiv ℝ S (t, r)
  let B := fderiv ℝ ((Φ t).symm : V → V) y
  have hq : DifferentiableAt ℝ q t :=
    ((diffeomorph_family_symm_contDiffAt hJ hc (p := (t, y)) ht).comp t
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
  have hS : HasFDerivAt S L (t, r) :=
    ((hc.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ r⟩)).differentiableAt
      (by norm_num)).hasFDerivAt
  have htime' : L (1, 0) = v := by
    have hleft := hS.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t r))
    change HasDerivAt (fun a => Φ a ((Φ t).symm y)) (L (1, 0)) t at hleft
    exact hleft.unique htime
  have hΦs : ContDiff ℝ ∞ (Φ t : V → V) := contMDiff_iff_contDiff.mp (Φ t).contMDiff
  have hΨs : ContDiff ℝ ∞ ((Φ t).symm : V → V) :=
    contMDiff_iff_contDiff.mp (Φ t).symm.contMDiff
  have hspace : L ∘L ContinuousLinearMap.inr ℝ ℝ V = fderiv ℝ (Φ t : V → V) r := by
    exact (hS.comp r (hasFDerivAt_prodMk_right t r)).unique
      (hΦs.differentiable (by simp) r).hasFDerivAt
  have hchain : HasDerivAt (fun a => S (a, q a)) (L (1, deriv q t)) t := by
    simpa only [Function.comp_def, id_eq] using
      hS.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hq.hasDerivAt)
  have hconstant : HasDerivAt (fun a => S (a, q a)) 0 t := by
    have he : (fun a => S (a, q a)) = fun _ => y :=
      funext (fun a => (Φ a).apply_symm_apply y)
    rw [he]
    exact hasDerivAt_const t y
  have heq := hchain.unique hconstant
  have hlin : L (1, deriv q t) = v + fderiv ℝ (Φ t : V → V) r (deriv q t) := by
    rw [show ((1, deriv q t) : ℝ × V) = (1, 0) + (0, deriv q t) by ext <;> simp,
      map_add, htime']
    congr 1
    exact congrArg (fun A : V →L[ℝ] V => A (deriv q t)) hspace
  rw [hlin] at heq
  have hinverse (z : V) : B (fderiv ℝ (Φ t : V → V) r z) = z := by
    have hi := fderiv_comp r (hΨs.differentiable (by simp) (Φ t r))
      (hΦs.differentiable (by simp) r)
    have hid : ((Φ t).symm : V → V) ∘ (Φ t : V → V) = id :=
      funext (Φ t).symm_apply_apply
    rw [hid, fderiv_id] at hi
    have hy : Φ t r = y := (Φ t).apply_symm_apply y
    rw [hy] at hi
    exact (congrArg (fun A : V →L[ℝ] V => A z) hi).symm
  have hzero := congrArg B heq
  rw [map_add, map_zero, hinverse] at hzero
  have hdq : deriv q t = -(B v) := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hzero
  simpa only [hdq] using hq.hasDerivAt

end PoincareConjecture.M35.RadialGauge

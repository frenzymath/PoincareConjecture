import PoincareConjecture.Proofs.M35.RadialGauge.SmoothEuclideanGauge
import PoincareConjecture.Proofs.M03.Existence.PullbackConnectionNative
import Mathlib.Analysis.Calculus.ImplicitContDiff










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)



theorem diffeomorph_family_symm_contDiffAt_order {k : ℕ} (hk : 1 ≤ k)
    {Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) V V ∞} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ k (fun p : ℝ × V => Φ p.1 p.2) (J ×ˢ univ))
    {p : ℝ × V} (hp : p.1 ∈ J) :
    ContDiffAt ℝ k (fun z : ℝ × V => (Φ z.1).symm z.2) p := by
  have hk' : (1 : ℕ∞ω) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℕ∞ω) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hk')
  let r := (Φ p.1).symm p.2
  let H (z : (ℝ × V) × V) := Φ z.1.1 z.2 - z.1.2
  have hcAt : ContDiffAt ℝ k (fun z : ℝ × V => Φ z.1 z.2) (p.1, r) :=
    hc.contDiffAt ((hJ.prod isOpen_univ).mem_nhds ⟨hp, mem_univ r⟩)
  have hH : ContDiffAt ℝ k H (p, r) :=
    (hcAt.comp (p, r)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub contDiffAt_fst.snd
  have hvalue : H (p, r) = 0 := by
    simp only [H, r, (Φ p.1).apply_symm_apply, sub_self]
  have hs : ContDiff ℝ ∞ (Φ p.1 : V → V) := contMDiff_iff_contDiff.mp (Φ p.1).contMDiff
  have hpart : fderiv ℝ H (p, r) ∘L ContinuousLinearMap.inr ℝ (ℝ × V) V =
      fderiv ℝ (Φ p.1 : V → V) r := by
    have hfirst := (hH.differentiableAt hk0).hasFDerivAt.comp r
      (hasFDerivAt_prodMk_right p r)
    have hsecond := ((hs.differentiable (by simp) r).hasFDerivAt).sub_const p.2
    exact hfirst.unique hsecond
  have hinv : (fderiv ℝ H (p, r) ∘L ContinuousLinearMap.inr ℝ (ℝ × V) V).IsInvertible := by
    rw [hpart]
    have h := DiffeomorphNative.mfderiv_isInvertible (Φ p.1) r
    simpa only [mfderiv_eq_fderiv] using h
  let q := hH.implicitFunction hk0 hinv
  have hq : ContDiffAt ℝ k q p := hH.contDiffAt_implicitFunction hk0 hinv
  have heq : ∀ᶠ z in 𝓝 p, H (z, q z) = 0 := by
    simpa only [hvalue] using hH.eventually_apply_implicitFunction hk0 hinv
  apply hq.congr_of_eventuallyEq
  filter_upwards [heq] with z hz
  apply (Φ z.1).injective
  change Φ z.1 ((Φ z.1).symm z.2) = Φ z.1 (q z)
  rw [(Φ z.1).apply_symm_apply]
  exact (sub_eq_zero.mp hz).symm


theorem diffeomorph_family_symm_contDiffAt
    {Φ : ℝ → Diffeomorph (𝓡 n) (𝓡 n) V V ∞} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContDiffOn ℝ 1 (fun p : ℝ × V => Φ p.1 p.2) (J ×ˢ univ))
    {p : ℝ × V} (hp : p.1 ∈ J) :
    ContDiffAt ℝ 1 (fun z : ℝ × V => (Φ z.1).symm z.2) p :=
  diffeomorph_family_symm_contDiffAt_order (k := 1) le_rfl hJ hc hp

end PoincareConjecture.M35.RadialGauge

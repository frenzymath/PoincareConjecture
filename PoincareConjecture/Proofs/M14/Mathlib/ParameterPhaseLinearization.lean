import PoincareConjecture.Proofs.M09.SecondOrderLinearization








set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.M14

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem parameterDifferential_secondOrderLinearization
    {C : Set ℝ} {U : Set E} (hC : IsOpen C) (hU : IsOpen U)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ ∞ f (C ×ˢ U))
    (B : ℝ × (F × F) → F × F) {s : ℝ} {x : E}
    (hs : s ∈ C) (hx : x ∈ U) (v : E)
    (hB : DifferentiableAt ℝ B
      (s, (f (s, x), deriv (fun r => f (r, x)) s)))
    (hode : ∀ y ∈ U, HasDerivAt
      (fun r => (f (r, y), deriv (fun t => f (t, y)) r))
      (B (s, (f (s, y), deriv (fun t => f (t, y)) s))) s) :
    let Y : ℝ → F := fun r => fderiv ℝ (fun y => f (r, y)) x v
    deriv (deriv Y) s =
      (fderiv ℝ B (s, (f (s, x), deriv (fun r => f (r, x)) s))
        (0, (Y s, deriv Y s))).2 := by
  let L : ℝ → E := fun u => x + u • v
  have hL : ContDiff ℝ ∞ L := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hL0 : L 0 = x := by simp [L]
  let g : ℝ × ℝ → F := fun z => f (z.1, L z.2)
  let V : Set (ℝ × ℝ) := C ×ˢ (L ⁻¹' U)
  have hV : IsOpen V := hC.prod (hU.preimage hL.continuous)
  have hsg : (s, 0) ∈ V := ⟨hs, by simpa only [Set.mem_preimage, hL0] using hx⟩
  have hg : ContDiffOn ℝ ∞ g V := hf.comp
    (contDiff_fst.prodMk (hL.comp contDiff_snd)).contDiffOn
    (fun _ hz => hz)
  have hBg : DifferentiableAt ℝ B
      (s, Proofs.M09.timeDerivativePhase g (s, 0)) := by
    simpa only [Proofs.M09.timeDerivativePhase, g, hL0] using hB
  have hodeg : ∀ᶠ u in 𝓝 (0 : ℝ), HasDerivAt
      (fun r => Proofs.M09.timeDerivativePhase g (r, u))
      (B (s, Proofs.M09.timeDerivativePhase g (s, u))) s := by
    filter_upwards [hL.continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by simpa only [hL0] using hx))] with u hu
    exact hode (L u) hu
  have hvar := Proofs.M09.hasDerivAt_variation_phase_of_ode
    g B V hV hg s hsg hBg hodeg
  let Y : ℝ → F := fun r => fderiv ℝ (fun y => f (r, y)) x v
  let Yg : ℝ → F := fun r => deriv (fun u => g (r, u)) 0
  have heq : Yg =ᶠ[𝓝 s] Y := by
    filter_upwards [hC.mem_nhds hs] with r hr
    have hfr : ContDiffOn ℝ ∞ (fun y => f (r, y)) U := hf.comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hy => ⟨hr, hy⟩)
    have hdL : HasDerivAt L v 0 := by
      simpa only [L, id_eq, one_smul] using
        ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    have hd := ((hfr.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
    exact (hd.comp_hasDerivAt_of_eq 0 hdL hL0.symm).deriv
  have hsecond : deriv (deriv Yg) s =
      (fderiv ℝ B (s, Proofs.M09.timeDerivativePhase g (s, 0))
        (0, (Yg s, deriv Yg s))).2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, ContinuousLinearMap.coe_snd'] using (hvar.hasFDerivAt.snd).hasDerivAt.deriv
  rw [heq.deriv.deriv_eq, heq.deriv_eq, heq.eq_of_nhds] at hsecond
  simpa only [Proofs.M09.timeDerivativePhase, g, hL0] using hsecond

end PoincareConjecture.M14

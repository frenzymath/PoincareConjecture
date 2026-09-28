import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Weighted.Energy
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.EnergyFlow
import Mathlib.Analysis.Calculus.Deriv.MeanValue













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable (D : LeviCivitaData g) (Ω : Set M) (hn : 0 < n)
  (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))

private theorem norm_domainMulL2_heatSemigroup_le
    (χ : M → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ) (L : ℝ)
    (hgrad : ∀ x ∈ Ω,
      g.inner x (D.gradient χ x) (D.gradient χ x) ≤ L ^ 2 * χ x ^ 2)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (t : ℝ) (ht : 0 ≤ t) :
    ‖domainMulL2 g Ω hΩ hc χ hχ.continuous (heatSemigroup D Ω hn hΩ hc t.toNNReal f)‖ ≤
      Real.exp (L ^ 2 * t) * ‖domainMulL2 g Ω hΩ hc χ hχ.continuous f‖ := by
  let A := domainMulL2 g Ω hΩ hc χ hχ.continuous
  let B := energyMulSmooth D Ω hc χ hχ
  let P (s : ℝ) := heatSemigroup D Ω hn hΩ hc s.toNNReal f
  let Q (s : ℝ) := heatSpectralPower D Ω hn hΩ hc 1 s f
  have hpair {s : ℝ} (hs : 0 < s) :
      -(L ^ 2) * ‖A (P s)‖ ^ 2 ≤ ⟪Q s, A (A (P s))⟫_ℝ := by
    let u := energyHeatSpectralPower D Ω hn hΩ hc 0 s f
    have hu : toDomainL2 D Ω u = P s := by
      dsimp [u, P]
      rw [toDomainL2_energyHeatSpectralPower D Ω hn hΩ hc 0 hs,
        heatSpectralPower_zero_eq_heatSemigroup D Ω hn hΩ hc hs]
    have hB (v : H1Zero D Ω) : toDomainL2 D Ω (B v) = A (toDomainL2 D Ω v) :=
      toDomainL2_energyMulSmooth hΩ hc χ hχ v
    have he := energyHeatSpectralPower_pairing D Ω hn hΩ hc 0 hs f (B (B u))
    have hb := twisted_energy_lower_bound hΩ hc χ hχ L hgrad u
    change -(L ^ 2) * ‖toDomainL2 D Ω (B u)‖ ^ 2 ≤
      ⟪u, B (B u)⟫_ℝ - ⟪toDomainL2 D Ω u, toDomainL2 D Ω (B (B u))⟫_ℝ at hb
    rw [hB, hB, hB, hu] at hb
    rw [heatSpectralPower_zero_eq_heatSemigroup D Ω hn hΩ hc hs] at he
    simp only [Nat.zero_add, hB, hu] at he
    exact hb.trans_eq he
  have hderiv {s : ℝ} (hs : 0 < s) :
      HasDerivAt (fun r => ‖A (P r)‖ ^ 2) (-2 * ⟪Q s, A (A (P s))⟫_ℝ) s := by
    have hd := A.hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_heatSemigroup D Ω hn hΩ hc hs f)
    have he : ⟪A (P s), A (Q s)⟫_ℝ = ⟪Q s, A (A (P s))⟫_ℝ := by
      rw [real_inner_comm]
      exact domainMulL2_inner hΩ hc χ hχ.continuous (Q s) (A (P s))
    convert hd.norm_sq using 1
    dsimp only [Function.comp_def]
    rw [map_neg, inner_neg_right]
    change -2 * ⟪Q s, A (A (P s))⟫_ℝ = 2 * -⟪A (P s), A (Q s)⟫_ℝ
    rw [he]
    ring
  let J (s : ℝ) := Real.exp (-2 * L ^ 2 * s) * ‖A (P s)‖ ^ 2
  let J' (s : ℝ) := Real.exp (-2 * L ^ 2 * s) *
    (-2 * L ^ 2 * ‖A (P s)‖ ^ 2 - 2 * ⟪Q s, A (A (P s))⟫_ℝ)
  have hdJ {s : ℝ} (hs : 0 < s) : HasDerivAt J (J' s) s := by
    have he := ((hasDerivAt_id s).const_mul (-2 * L ^ 2)).exp
    simp only [id_eq, mul_one] at he
    change HasDerivAt
      (fun r => Real.exp (-2 * L ^ 2 * r) * ‖A (P r)‖ ^ 2)
      (Real.exp (-2 * L ^ 2 * s) *
        (-2 * L ^ 2 * ‖A (P s)‖ ^ 2 - 2 * ⟪Q s, A (A (P s))⟫_ℝ)) s
    convert! he.mul (hderiv hs) using 1
    ring
  have hJ' {s : ℝ} (hs : 0 < s) : J' s ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    nlinarith [hpair hs]
  have hP : Continuous P :=
    (continuous_heatSemigroup D Ω hn hΩ hc f).comp (by fun_prop)
  have hJ : Continuous J := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((A.continuous.comp hP).norm.pow 2)
  have hanti : AntitoneOn J (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hJ.continuousOn
      (f' := J')
    · intro s hs
      exact (hdJ (by simpa only [interior_Ici, mem_Ioi] using hs)).hasDerivWithinAt
    · intro s hs
      exact hJ' (by simpa only [interior_Ici, mem_Ioi] using hs)
  have hbound := hanti (show (0 : ℝ) ∈ Ici 0 from by simp) ht ht
  have hzero : P 0 = f := by simp [P]
  change J t ≤ J 0 at hbound
  dsimp only [J] at hbound
  rw [hzero, mul_zero, Real.exp_zero, one_mul] at hbound
  have hsquare : ‖A (P t)‖ ^ 2 ≤ (Real.exp (L ^ 2 * t) * ‖A f‖) ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (2 * L ^ 2 * t))
    have he : Real.exp (2 * L ^ 2 * t) * Real.exp (-2 * L ^ 2 * t) = 1 := by
      rw [← Real.exp_add]
      rw [show 2 * L ^ 2 * t + -2 * L ^ 2 * t = 0 by ring, Real.exp_zero]
    rw [← mul_assoc, he, one_mul] at hm
    have he₂ : Real.exp (L ^ 2 * t) ^ 2 = Real.exp (2 * L ^ 2 * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa only [mul_pow, he₂] using hm
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp hsquare


theorem weighted_heatSemigroup_norm_le
    (ψ : M → ℝ) (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ)
    (L : ℝ) (_hL : 0 ≤ L)
    (hgrad : ∀ x ∈ Ω, g.inner x (D.gradient ψ x) (D.gradient ψ x) ≤ L ^ 2)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (t : ℝ) (ht : 0 < t) :
    (eLpNorm (fun x => Real.exp (ψ x) * heatSemigroup D Ω hn hΩ hc t.toNNReal f x)
      2 (g.volumeMeasure.restrict Ω)).toReal ≤
      Real.exp (L ^ 2 * t) *
        (eLpNorm (fun x => Real.exp (ψ x) * f x)
          2 (g.volumeMeasure.restrict Ω)).toReal := by
  have he : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => Real.exp (ψ x)) :=
    Real.contDiff_exp.contMDiff.comp hψ
  have h := norm_domainMulL2_heatSemigroup_le D Ω hn hΩ hc
    (fun x => Real.exp (ψ x)) he L (gradient_exp_weight_bound ψ hψ hgrad) f t ht.le
  simpa only [norm_domainMulL2] using h

end PoincareConjecture.LeviCivitaData.Dirichlet

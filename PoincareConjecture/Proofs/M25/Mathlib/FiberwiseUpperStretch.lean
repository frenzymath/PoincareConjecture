import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseDiffeomorph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v w

theorem Diffeomorph.exists_fiberwise_upper_stretch
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {H : Type v} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {K : Type w} [TopologicalSpace K] [ChartedSpace H K]
    [IsManifold I ∞ K]
    (L : ℝ) (hL : 0 < L) (upper : K → ℝ)
    (hupper : ContMDiff I 𝓘(ℝ, ℝ) ∞ upper)
    (hbound : ∀ q : K, L ≤ upper q) :
    ∃ G : Diffeomorph (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ))
        (K × ℝ) (K × ℝ) ∞,
      (∀ z : K × ℝ,
        G z = (z.1, z.2 + (upper z.1 - L) *
          Real.smoothTransition (2 * z.2 / L))) ∧
      (∀ z : K × ℝ, (G.symm z).1 = z.1) ∧
      EqOn (G : K × ℝ → K × ℝ) id (univ ×ˢ Iic (0 : ℝ)) ∧
      EqOn (G.symm : K × ℝ → K × ℝ) id (univ ×ˢ Iic (0 : ℝ)) ∧
      (G : K × ℝ → K × ℝ) '' (univ ×ˢ Ioo (-L) L) =
        {z : K × ℝ | -L < z.2 ∧ z.2 < upper z.1} ∧
      (G : K × ℝ → K × ℝ) ⁻¹'
          {z : K × ℝ | -L < z.2 ∧ z.2 < upper z.1} =
        univ ×ˢ Ioo (-L) L := by
  classical
  let beta : ℝ → ℝ := fun t => Real.smoothTransition (2 * t / L)
  have hbeta : ContDiff ℝ ∞ beta :=
    Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul contDiff_id).div_const L)
  have hmonoBeta : Monotone beta := by
    intro x y hxy
    exact Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (by norm_num)) hL.le)
  have hbetaNonneg (t : ℝ) : 0 ≤ beta t := Real.smoothTransition.nonneg _
  have hbetaLe (t : ℝ) : beta t ≤ 1 := Real.smoothTransition.le_one _
  have hbetaZero (t : ℝ) (ht : t ≤ 0) : beta t = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) ht) hL.le)
  have hbetaL : beta L = 1 :=
    Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hL).mpr (by linarith))
  let f : K × ℝ → ℝ := fun z => z.2 + (upper z.1 - L) * beta z.2
  have houter : ContDiff ℝ ∞
      (fun z : ℝ × ℝ => z.2 + (z.1 - L) * beta z.2) :=
    contDiff_snd.add
      ((contDiff_fst.sub contDiff_const).mul (hbeta.comp contDiff_snd))
  have hpair : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun z : K × ℝ => (upper z.1, z.2)) :=
    (hupper.comp contMDiff_fst).prodMk_space contMDiff_snd
  have hf : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ f :=
    houter.comp_contMDiff hpair
  have hnonneg (q : K) : 0 ≤ upper q - L := sub_nonneg.mpr (hbound q)
  have hpos (q : K) (t : ℝ) : 0 < deriv (fun r : ℝ => f (q, r)) t := by
    have hb : HasDerivAt beta (deriv beta t) t :=
      ((hbeta.differentiable (by simp)) t).hasDerivAt
    have hd := (hasDerivAt_id t).add (hb.const_mul (upper q - L))
    have hderiv : deriv (fun r : ℝ => r + (upper q - L) * beta r) t =
        1 + (upper q - L) * deriv beta t := by
      simpa only [Pi.add_def, id_eq] using hd.deriv
    change 0 < deriv (fun r : ℝ => r + (upper q - L) * beta r) t
    rw [hderiv]
    have hp : 0 ≤ (upper q - L) * deriv beta t :=
      mul_nonneg (hnonneg q) hmonoBeta.deriv_nonneg
    linarith
  have hlower (q : K) (t : ℝ) : t ≤ f (q, t) :=
    le_add_of_nonneg_right (mul_nonneg (hnonneg q) (hbetaNonneg t))
  have hupperFiber (q : K) (t : ℝ) : f (q, t) ≤ t + (upper q - L) := by
    have h := mul_le_mul_of_nonneg_left (hbetaLe t) (hnonneg q)
    simpa only [f, mul_one, add_comm] using add_le_add_left h t
  have hsurj (q : K) : Function.Surjective (fun t : ℝ => f (q, t)) := by
    intro y
    have hc : Continuous (fun t : ℝ => f (q, t)) := by
      change Continuous (fun t : ℝ => t + (upper q - L) * beta t)
      have ha : Continuous (fun _ : ℝ => upper q - L) := continuous_const
      exact continuous_id.add (ha.mul hbeta.continuous)
    exact mem_range_of_exists_le_of_exists_ge hc
      ⟨y - (upper q - L), by
        have h := hupperFiber q (y - (upper q - L))
        linarith⟩
      ⟨y, hlower q y⟩
  have hmono (q : K) : StrictMono (fun t : ℝ => f (q, t)) :=
    strictMono_of_deriv_pos (hpos q)
  have hfLower (q : K) : f (q, -L) = -L := by
    simp only [f, hbetaZero (-L) (neg_nonpos.mpr hL.le), mul_zero, add_zero]
  have hfUpper (q : K) : f (q, L) = upper q := by
    simp only [f, hbetaL, mul_one]
    ring
  obtain ⟨G, hG, hGi⟩ :=
    Diffeomorph.exists_fiberwise_of_deriv_pos (Diffeomorph.refl I K ∞) f hf hpos hsurj
  have hformula (z : K × ℝ) : G z = (z.1, f z) := by
    simpa only [Diffeomorph.coe_refl, id_eq] using hG z
  have hfix : EqOn (G : K × ℝ → K × ℝ) id (univ ×ˢ Iic (0 : ℝ)) := by
    intro z hz
    change G z = z
    rw [hformula]
    apply Prod.ext
    · rfl
    · change z.2 + (upper z.1 - L) * beta z.2 = z.2
      rw [hbetaZero z.2 hz.2, mul_zero, add_zero]
  have hfixInv : EqOn (G.symm : K × ℝ → K × ℝ) id
      (univ ×ˢ Iic (0 : ℝ)) := by
    intro z hz
    change G.symm z = z
    calc
      G.symm z = G.symm (G z) := congrArg G.symm (hfix hz).symm
      _ = z := G.symm_apply_apply z
  have hmem (z : K × ℝ) :
      G z ∈ {y : K × ℝ | -L < y.2 ∧ y.2 < upper y.1} ↔
        z ∈ univ ×ˢ Ioo (-L) L := by
    rw [hformula]
    have hlo := (hmono z.1).lt_iff_lt (a := -L) (b := z.2)
    have hhi := (hmono z.1).lt_iff_lt (a := z.2) (b := L)
    rw [hfLower] at hlo
    rw [hfUpper] at hhi
    change (-L < f (z.1, z.2) ∧ f (z.1, z.2) < upper z.1) ↔
      z.1 ∈ univ ∧ (-L < z.2 ∧ z.2 < L)
    constructor
    · intro hz
      exact ⟨mem_univ _, hlo.mp hz.1, hhi.mp hz.2⟩
    · intro hz
      exact ⟨hlo.mpr hz.2.1, hhi.mpr hz.2.2⟩
  have hpreimage : (G : K × ℝ → K × ℝ) ⁻¹'
      {z : K × ℝ | -L < z.2 ∧ z.2 < upper z.1} =
        univ ×ˢ Ioo (-L) L := by
    ext z
    exact hmem z
  have himage : (G : K × ℝ → K × ℝ) '' (univ ×ˢ Ioo (-L) L) =
      {z : K × ℝ | -L < z.2 ∧ z.2 < upper z.1} := by
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact (hmem z).mpr hz
    · intro y hy
      refine ⟨G.symm y, (hmem (G.symm y)).mp ?_, G.apply_symm_apply y⟩
      simpa only [G.apply_symm_apply] using hy
  refine ⟨G, ?_, ?_, hfix, hfixInv, himage, hpreimage⟩
  · intro z
    simpa only [f, beta] using hformula z
  · intro z
    simpa only [Diffeomorph.symm_refl, Diffeomorph.coe_refl, id_eq] using (hGi z).1

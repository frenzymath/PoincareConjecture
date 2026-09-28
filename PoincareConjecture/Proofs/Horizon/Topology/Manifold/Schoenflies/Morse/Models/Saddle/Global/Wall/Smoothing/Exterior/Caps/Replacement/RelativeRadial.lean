import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Radial
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.LocalExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private instance : Fact (Module.finrank Real E3 = 2 + 1) := ⟨by simp⟩

theorem exists_relative_radial_upper_cap_transport
    (r₀ r₁ : S2 → Real)
    (hr₀ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ r₀)
    (hr₁ : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ r₁)
    (hpos₀ : ∀ p, 0 < r₀ p) (hpos₁ : ∀ p, 0 < r₁ p)
    {ε : Real} (hε : 0 < ε)
    (heq : ∀ p : S2, (p : E3) 2 ∈ Icc (0 : Real) ε → r₀ p = r₁ p) :
    ∃ (η : Real) (E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞),
      0 < η ∧ (∀ x : E3, x 2 ≤ η → E x = x) ∧
      (∃ K : Set E3, IsCompact K ∧ ∀ x ∉ K, E x = x) ∧
      ∀ p : S2, 0 ≤ (p : E3) 2 → E (r₀ p • (p : E3)) = r₁ p • (p : E3) := by
  let a : S2 → Real := fun p => Real.log (r₁ p) - Real.log (r₀ p)
  have hlog (r : S2 → Real) (hr : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ r)
      (hp : ∀ p, 0 < r p) : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun p => Real.log (r p)) := by
    intro p
    exact (Real.contDiffAt_log.mpr (hp p).ne').contMDiffAt.comp p (hr p)
  have ha : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ a := (hlog _ hr₁ hpos₁).sub (hlog _ hr₀ hpos₀)
  let b : Real × S2 → Real := fun z => r₀ z.2 * Real.exp (z.1 * a z.2)
  have hb : Continuous b := (hr₀.continuous.comp continuous_snd).mul
    (continuous_fst.mul (ha.continuous.comp continuous_snd)).rexp
  have hbpos (t : Real) (p : S2) : 0 < b (t, p) := mul_pos (hpos₀ p) (Real.exp_pos _)
  let p₀ : S2 := ⟨EuclideanSpace.single 2 1, by simp⟩
  obtain ⟨z₀, _, hmin⟩ := (isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set S2))).exists_isMinOn
    (show (Icc (0 : Real) 1 ×ˢ (univ : Set S2)).Nonempty from ⟨(0, p₀), by simp⟩)
    hb.continuousOn
  let m := b z₀
  have hm : 0 < m := hbpos z₀.1 z₀.2
  have hmb (t : Real) (ht : t ∈ Icc (0 : Real) 1) (p : S2) : m ≤ b (t, p) :=
    hmin ⟨ht, mem_univ p⟩
  let η := m * ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  let U : TopologicalSpace.Opens E3 := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  let radial : U → S2 := fun x =>
    ⟨‖x.val‖⁻¹ • x.val, by simp [norm_smul, norm_ne_zero_iff.mpr x.property]⟩
  have hn : ContMDiff (𝓡 3) 𝓘(Real, Real) ∞ (fun x : U => ‖x.val‖) := by
    intro x
    exact (contDiffAt_norm Real x.property).contMDiffAt.comp x (contMDiff_subtype_val x)
  have hr : ContMDiff (𝓡 3) (𝓡 2) ∞ radial :=
    ((hn.inv₀ (fun x => norm_ne_zero_iff.mpr x.property)).smul
      contMDiff_subtype_val).codRestrict_sphere _
  let V : E3 → E3 := fun x => if hx : x = 0 then 0 else a (radial ⟨x, hx⟩) • x
  have hV : ContDiffOn Real ∞ V U := by
    intro x hx
    have hs : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => V y.val) := by
      convert (ha.comp hr).smul contMDiff_subtype_val using 1
      funext y
      exact dif_neg y.property
    exact (contMDiffAt_subtype_iff.mp (hs ⟨x, hx⟩)).contDiffAt.contDiffWithinAt
  let g : Real × S2 → E3 := fun z => b z • (z.2 : E3)
  have hg : Continuous g := hb.smul (continuous_subtype_val.comp continuous_snd)
  let P : Set S2 := {p | ε / 2 ≤ (p : E3) 2}
  have hP : IsCompact P := (isClosed_le continuous_const (by fun_prop)).isCompact
  let K := g '' (Icc (0 : Real) 1 ×ˢ P)
  have hK : IsCompact K := (isCompact_Icc.prod hP).image hg
  let O : Set E3 := {x | η < x 2}
  have hO : IsOpen O := isOpen_lt continuous_const (by fun_prop)
  have hOU : O ⊆ U := by
    intro x hx hzero
    change η < x 2 at hx
    rw [hzero] at hx
    simp only [PiLp.zero_apply] at hx
    linarith
  have hKO : K ⊆ O := by
    rintro x ⟨⟨t, p⟩, ⟨ht, hp⟩, rfl⟩
    change η < b (t, p) * (p : E3) 2
    have hp' : ε / 2 ≤ (p : E3) 2 := hp
    have hm' := hmb t ht p
    have hb' := hbpos t p
    dsimp [η]
    nlinarith
  obtain ⟨χ, hχ, hχc, hχO, hχK⟩ :=
    Poincare.Parabolic.Interior.exists_contDiff_compact_cutoff hK hO hKO
  let W : E3 → E3 := fun x => χ x • V x
  have hW : ContDiff Real ∞ W :=
    Poincare.Parabolic.Interior.contDiff_smul_cutoff hO (hV.mono hOU) hχ hχO
  have hWc : HasCompactSupport W := hχc.smul_right
  obtain ⟨Φ, hi, hs, ho, hfix⟩ :=
    exists_diffeomorph_evolution_of_compact_spatial_support
      (fun z : Real × E3 => W z.2) (hW.comp contDiff_snd) hχc.isCompact
      (fun _ x hx => by change χ x • V x = 0; rw [image_eq_zero_of_notMem_tsupport hx, zero_smul])
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hWc hW (by simp)
  refine ⟨η, Φ 0 1, hη, ?_, ⟨tsupport χ, hχc.isCompact, hfix 0 1⟩, ?_⟩
  · intro x hx
    exact hfix 0 1 x (fun h => (not_lt_of_ge hx) (hχO h))
  · intro p hp
    have hgne (t : Real) : g (t, p) ≠ 0 := smul_ne_zero (hbpos t p).ne' (ne_zero_of_mem_unit_sphere p)
    have hradial (t : Real) : radial ⟨g (t, p), hgne t⟩ = p := by
      apply Subtype.ext
      change ‖b (t, p) • (p : E3)‖⁻¹ • (b (t, p) • (p : E3)) = (p : E3)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hbpos t p), norm_eq_of_mem_sphere,
        mul_one, smul_smul, inv_mul_cancel₀ (hbpos t p).ne', one_smul]
    have hVg (t : Real) : V (g (t, p)) = (a p * b (t, p)) • (p : E3) := by
      change (if hx : g (t, p) = 0 then 0 else a (radial ⟨g (t, p), hx⟩) • g (t, p)) = _
      rw [dif_neg (hgne t), hradial]
      exact smul_smul _ _ _
    have hvel (t : Real) (ht : t ∈ Icc (0 : Real) 1) :
        W (g (t, p)) = (a p * b (t, p)) • (p : E3) := by
      change χ (g (t, p)) • V (g (t, p)) = _
      rw [hVg]
      by_cases hpP : p ∈ P
      · rw [(hχK _ ⟨(t, p), ⟨ht, hpP⟩, rfl⟩).eq_of_nhds, one_smul]
      · have ha0 : a p = 0 := by
          have hp' : ¬ ε / 2 ≤ (p : E3) 2 := hpP
          dsimp [a]
          rw [heq p ⟨hp, by linarith⟩, sub_self]
        rw [ha0, zero_mul, zero_smul, smul_zero]
    have hder (t : Real) : HasDerivAt (fun t => g (t, p))
        ((a p * b (t, p)) • (p : E3)) t := by
      convert! ((((hasDerivAt_id t).mul_const (a p)).exp).const_mul (r₀ p)).smul_const (p : E3) using 1
      dsimp [g, b]
      congr 1
      ring
    have he := ODE_solution_unique (v := fun _ => W) (fun _ => hL)
      (f := fun t => Φ 0 t (r₀ p • (p : E3))) (g := fun t => g (t, p))
      ((hs 0).continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t _ => (ho 0 (r₀ p • (p : E3)) t).hasDerivWithinAt)
      (hg.comp (continuous_id.prodMk continuous_const)).continuousOn
      (fun t ht => by rw [hvel t (Ico_subset_Icc_self ht)]; exact (hder t).hasDerivWithinAt)
      (by simp [hi, g, b])
    have hb1 : b (1, p) = r₁ p := by
      dsimp [b, a]
      rw [one_mul, Real.exp_sub, Real.exp_log (hpos₁ p), Real.exp_log (hpos₀ p)]
      field_simp [(hpos₀ p).ne']
    simpa only [g, hb1] using he (show (1 : Real) ∈ Icc 0 1 by simp)

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps

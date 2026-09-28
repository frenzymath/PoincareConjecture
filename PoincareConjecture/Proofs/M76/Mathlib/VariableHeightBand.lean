import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHeightBand
import PoincareConjecture.Proofs.M76.Mathlib.PulledBackHeightBandSection

set_option autoImplicit false

open Set Geometry
open scoped NNReal

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.exists_uniform_band_lipschitzOnWith
    {f : E × ℝ → F} {B : Set E} {lower upper : E → ℝ}
    (hf : FinitePiecewiseAffineOn f
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}) :
    ∃ L : ℝ≥0, ∀ x ∈ B,
      LipschitzOnWith L (fun t => f (x, t)) (Icc (lower x) (upper x)) := by
  obtain ⟨L, hL⟩ := hf.exists_uniform_convex_lipschitzOnWith
  refine ⟨L, fun x hx => LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_⟩
  have hsubset : ({x} ×ˢ Icc (lower x) (upper x) : Set (E × ℝ)) ⊆
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have hyx : y = x := hy
    subst y
    exact ⟨hx, ht⟩
  have h := (hL ({x} ×ˢ Icc (lower x) (upper x)) hsubset
    ((convex_singleton x).prod (convex_Icc _ _))).dist_le_mul
      (x, u) ⟨mem_singleton x, hu⟩ (x, v) ⟨mem_singleton x, hv⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist u v)] using h

theorem FinitePiecewiseAffineOn.exists_strictMonoOn_band_perturbation
    {g : E × ℝ → ℝ} {B : Set E} {lower upper : E → ℝ}
    (hg : FinitePiecewiseAffineOn g
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ x ∈ B,
      StrictMonoOn (fun t => t + ε * g (x, t)) (Icc (lower x) (upper x)) := by
  obtain ⟨L, hL⟩ := hg.exists_uniform_band_lipschitzOnWith
  let δ : ℝ := 1 / ((L : ℝ) + 1)
  have hden : 0 < (L : ℝ) + 1 := by positivity
  refine ⟨δ, one_div_pos.mpr hden, fun ε hε x hx => (hL x hx).strictMonoOn_id_add_mul ?_⟩
  have hsmall : |ε| * ((L : ℝ) + 1) < 1 := (lt_div_iff₀ hden).mp hε
  nlinarith [abs_nonneg ε]

theorem FinitePiecewiseAffineOn.exists_variable_heightBand_homeomorph
    {g : E × ℝ → ℝ} {B : Set E} {lower upper : E → ℝ}
    (hlu : ∀ x ∈ B, lower x ≤ upper x)
    (hg : FinitePiecewiseAffineOn g
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ →
      ∃ H : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} ≃ₜ
          {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈
            Icc (lower p.1 + ε * g (p.1, lower p.1))
              (upper p.1 + ε * g (p.1, upper p.1))},
        H.IsFinitePL ∧ ∀ p, (H p : E × ℝ) =
          ((p : E × ℝ).1, (p : E × ℝ).2 + ε * g p) := by
  obtain ⟨δ, hδ, hmono⟩ := hg.exists_strictMonoOn_band_perturbation
  refine ⟨δ, hδ, fun ε hε => ?_⟩
  let S : Set (E × ℝ) := {p | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}
  let f : E × ℝ → E × ℝ := fun p => (p.1, p.2 + ε * g p)
  have hinj : InjOn f S := by
    rintro ⟨x, u⟩ hp ⟨y, v⟩ hq heq
    have hxy : x = y := congrArg Prod.fst heq
    subst y
    exact Prod.ext rfl ((hmono ε hε x hp.1).injOn hp.2 hq.2 (congrArg Prod.snd heq))
  have himage : f '' S = {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈
      Icc (lower p.1 + ε * g (p.1, lower p.1))
        (upper p.1 + ε * g (p.1, upper p.1))} := by
    ext p
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      refine ⟨hx, ?_, ?_⟩
      · exact (hmono ε hε x hx).monotoneOn ⟨le_rfl, hlu x hx⟩ ht ht.1
      · exact (hmono ε hε x hx).monotoneOn ht ⟨hlu x hx, le_rfl⟩ ht.2
    · rintro ⟨hx, ht⟩
      have hgc : ContinuousOn (fun t => g (p.1, t)) (Icc (lower p.1) (upper p.1)) :=
        hg.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun t ht => ⟨hx, ht⟩)
      have hc : ContinuousOn (fun t => t + ε * g (p.1, t))
          (Icc (lower p.1) (upper p.1)) :=
        continuousOn_id.add (continuousOn_const.mul hgc)
      obtain ⟨t, htd, htv⟩ := intermediate_value_Icc (hlu p.1 hx) hc ht
      exact ⟨(p.1, t), ⟨hx, htd⟩, Prod.ext rfl htv⟩
  obtain ⟨G, hG, hGval⟩ := (hg.heightChange ε).exists_homeomorph_image hinj
  exact ⟨(Homeomorph.setCongr (rfl : S = S)).trans
    (G.trans (Homeomorph.setCongr himage)), hG.setCongr rfl himage, fun p => hGval p⟩

theorem FinitePiecewiseAffineOn.exists_variable_band_level_charts [FiniteDimensional ℝ E]
    {g : E × ℝ → ℝ} {B : Set E} {lower upper : E → ℝ}
    (hlu : ∀ x ∈ B, lower x ≤ upper x)
    (hg : FinitePiecewiseAffineOn g
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)}) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ c : ℝ,
      ∃ H : {x : E | x ∈ B ∧ c ∈ Icc (lower x + ε * g (x, lower x))
          (upper x + ε * g (x, upper x))} ≃ₜ
        ({p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc (lower p.1) (upper p.1)} ∩
          {p : E × ℝ | p.2 + ε * g p = c} : Set (E × ℝ)),
        H.IsFinitePL ∧ ∀ x, (H x : E × ℝ).1 = (x : E) := by
  obtain ⟨δ, hδ, hbands⟩ := hg.exists_variable_heightBand_homeomorph hlu
  refine ⟨δ, hδ, fun ε hε c => ?_⟩
  obtain ⟨H, hH, hval⟩ := hbands ε hε
  exact hH.exists_heightBand_level_chart hval c

end Geometry

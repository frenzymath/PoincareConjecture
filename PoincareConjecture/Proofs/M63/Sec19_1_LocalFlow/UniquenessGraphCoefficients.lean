import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactJetBounds
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessGraphComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff RealInnerProductSpace

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι
local notation "G" => ℝ × (W × W)

theorem isOpen_curveGraphJetDomain (F : RicciFlow n M (Icc a b))
    {V : Set W} (hV : IsOpen V) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ V)
    {r : ℝ → W} (hr : ContDiff ℝ ∞ r) :
    IsOpen {z : G | r z.1 + z.2.1 ∈ V ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r z.1 + z.2.1) (deriv r z.1 + z.2.2) ≠ 0 ∧
      ⟪deriv r z.1 + z.2.2, deriv r z.1⟫ ≠ 0} := by
  have hr₁ := (contDiff_infty_iff_deriv.mp hr).2
  have hC : Continuous (fun z : G => r z.1 + z.2.1) :=
    (hr.continuous.comp continuous_fst).add continuous_snd.fst
  have hX : Continuous (fun z : G => deriv r z.1 + z.2.2) :=
    (hr₁.continuous.comp continuous_fst).add continuous_snd.snd
  have hd : Continuous (fun z : G => ⟪deriv r z.1 + z.2.2, deriv r z.1⟫) :=
    hX.inner (hr₁.continuous.comp continuous_fst)
  have hopen := ((isOpen_ambientCurveJetDomain F hV hρ).preimage (hC.prodMk hX)).inter
    (isOpen_ne_fun (g := fun _ => (0 : ℝ)) hd continuous_const)
  convert hopen using 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, and_assoc]

theorem curveGraphCoefficients_contDiffOn (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {V : Set W} (hV : IsOpen V) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ V)
    {r : ℝ → W} (hr : ContDiff ℝ ∞ r) :
    let Ω : Set G := {z | r z.1 + z.2.1 ∈ V ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r z.1 + z.2.1) (deriv r z.1 + z.2.2) ≠ 0 ∧
      ⟪deriv r z.1 + z.2.2, deriv r z.1⟫ ≠ 0}
    let A : ℝ × G → ℝ := fun z => ambientCurvePrincipal F ρ z.1
      (r z.2.1 + z.2.2.1) (deriv r z.2.1 + z.2.2.2)
    let B : ℝ × G → W := fun z => curveGraphLower (A z)
      (ambientCurveLower F e ρ z.1 (r z.2.1 + z.2.2.1) (deriv r z.2.1 + z.2.2.2))
      (deriv r z.2.1) (deriv (deriv r) z.2.1) (deriv (deriv (deriv r)) z.2.1)
      z.2.2.1 z.2.2.2
    ContDiffOn ℝ ∞ A (Icc a b ×ˢ Ω) ∧ ContDiffOn ℝ ∞ B (Icc a b ×ˢ Ω) ∧
      ∀ t z, z ∈ Ω → 0 < A (t, z) := by
  let Ω : Set G := {z | r z.1 + z.2.1 ∈ V ∧
    mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r z.1 + z.2.1) (deriv r z.1 + z.2.2) ≠ 0 ∧
    ⟪deriv r z.1 + z.2.2, deriv r z.1⟫ ≠ 0}
  let A : ℝ × G → ℝ := fun z => ambientCurvePrincipal F ρ z.1
    (r z.2.1 + z.2.2.1) (deriv r z.2.1 + z.2.2.2)
  let B₀ : ℝ × G → W := fun z => ambientCurveLower F e ρ z.1
    (r z.2.1 + z.2.2.1) (deriv r z.2.1 + z.2.2.2)
  let B : ℝ × G → W := fun z => curveGraphLower (A z) (B₀ z)
    (deriv r z.2.1) (deriv (deriv r) z.2.1) (deriv (deriv (deriv r)) z.2.1)
    z.2.2.1 z.2.2.2
  change ContDiffOn ℝ ∞ A (Icc a b ×ˢ Ω) ∧ ContDiffOn ℝ ∞ B (Icc a b ×ˢ Ω) ∧
    ∀ t z, z ∈ Ω → 0 < A (t, z)
  have hr₁ := (contDiff_infty_iff_deriv.mp hr).2
  have hr₂ := (contDiff_infty_iff_deriv.mp hr₁).2
  have hr₃ := (contDiff_infty_iff_deriv.mp hr₂).2
  have hy : ContDiff ℝ ∞ (fun z : ℝ × G => z.2.1) := contDiff_snd.fst
  have hu : ContDiff ℝ ∞ (fun z : ℝ × G => z.2.2.1) := contDiff_snd.snd.fst
  have hp : ContDiff ℝ ∞ (fun z : ℝ × G => z.2.2.2) := contDiff_snd.snd.snd
  have hC : ContDiff ℝ ∞ (fun z : ℝ × G => r z.2.1 + z.2.2.1) :=
    (hr.comp hy).add hu
  have hX : ContDiff ℝ ∞ (fun z : ℝ × G => deriv r z.2.1 + z.2.2.2) :=
    (hr₁.comp hy).add hp
  have hparam : ContDiff ℝ ∞ (fun z : ℝ × G =>
      ((z.1, r z.2.1 + z.2.2.1), deriv r z.2.1 + z.2.2.2)) :=
    (contDiff_fst.prodMk hC).prodMk hX
  obtain ⟨hAraw, hBraw, hpos⟩ := ambientCurveCoefficients_contDiffOn F he hV hρ
  have hAcomp := hAraw.comp (s := Icc a b ×ˢ Ω) hparam.contDiffOn
    (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.1⟩)
  have hA : ContDiffOn ℝ ∞ A (Icc a b ×ˢ Ω) := hAcomp
  have hBcomp := hBraw.comp (s := Icc a b ×ˢ Ω) hparam.contDiffOn
    (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.1⟩)
  have hB₀ : ContDiffOn ℝ ∞ B₀ (Icc a b ×ˢ Ω) := hBcomp
  have hr₁p : ContDiffOn ℝ ∞ (fun z : ℝ × G => deriv r z.2.1) (Icc a b ×ˢ Ω) :=
    (hr₁.comp hy).contDiffOn
  have hr₂p : ContDiffOn ℝ ∞ (fun z : ℝ × G => deriv (deriv r) z.2.1)
      (Icc a b ×ˢ Ω) := (hr₂.comp hy).contDiffOn
  have hr₃p : ContDiffOn ℝ ∞ (fun z : ℝ × G => deriv (deriv (deriv r)) z.2.1)
      (Icc a b ×ˢ Ω) := (hr₃.comp hy).contDiffOn
  have hu' := hu.contDiffOn (s := Icc a b ×ˢ Ω)
  have hp' := hp.contDiffOn (s := Icc a b ×ˢ Ω)
  have hX' := hX.contDiffOn (s := Icc a b ×ˢ Ω)
  have hnum : ContDiffOn ℝ ∞ (fun z : ℝ × G =>
      -(A z * (⟪deriv (deriv r) z.2.1, deriv r z.2.1⟫ -
        2 * ⟪z.2.2.2, deriv (deriv r) z.2.1⟫ -
        ⟪z.2.2.1, deriv (deriv (deriv r)) z.2.1⟫) + ⟪B₀ z, deriv r z.2.1⟫))
      (Icc a b ×ˢ Ω) :=
    ((hA.mul (((hr₂p.inner ℝ hr₁p).sub (contDiffOn_const.mul (hp'.inner ℝ hr₂p))).sub
      (hu'.inner ℝ hr₃p))).add (hB₀.inner ℝ hr₁p)).neg
  have hquot := hnum.div (hX'.inner ℝ hr₁p) (fun z hz => hz.2.2.2)
  have hB : ContDiffOn ℝ ∞ B (Icc a b ×ˢ Ω) :=
    ((hA.smul hr₂p).add hB₀).add (hquot.smul hX')
  exact ⟨hA, hB, fun t z hz => hpos t _ hz.1 _ hz.2.1⟩

theorem curveGraphCoefficients_uniform_bounds (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {V : Set W} (hV : IsOpen V) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ V)
    {r : ℝ → W} (hr : ContDiff ℝ ∞ r) {K : Set G} (hK : IsCompact K)
    (hsub : K ⊆ {z : G | r z.1 + z.2.1 ∈ V ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r z.1 + z.2.1) (deriv r z.1 + z.2.2) ≠ 0 ∧
      ⟪deriv r z.1 + z.2.2, deriv r z.1⟫ ≠ 0}) :
    let A : ℝ × G → ℝ := fun z => ambientCurvePrincipal F ρ z.1
      (r z.2.1 + z.2.2.1) (deriv r z.2.1 + z.2.2.2)
    let B : ℝ × G → W := fun z => curveGraphLower (A z)
      (ambientCurveLower F e ρ z.1 (r z.2.1 + z.2.2.1) (deriv r z.2.1 + z.2.2.2))
      (deriv r z.2.1) (deriv (deriv r) z.2.1) (deriv (deriv (deriv r)) z.2.1)
      z.2.2.1 z.2.2.2
    ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧ ∃ L_A L_B : NNReal,
      (∀ t ∈ Icc a b, ∀ z ∈ K, mu ≤ A (t, z) ∧ A (t, z) ≤ Lambda) ∧
      (∀ t ∈ Icc a b, LipschitzOnWith L_A (fun z => A (t, z)) K) ∧
      (∀ t ∈ Icc a b, LipschitzOnWith L_B (fun z => B (t, z)) K) := by
  let Ω : Set G := {z | r z.1 + z.2.1 ∈ V ∧
    mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (r z.1 + z.2.1) (deriv r z.1 + z.2.2) ≠ 0 ∧
    ⟪deriv r z.1 + z.2.2, deriv r z.1⟫ ≠ 0}
  let A : ℝ × G → ℝ := fun z => ambientCurvePrincipal F ρ z.1
    (r z.2.1 + z.2.2.1) (deriv r z.2.1 + z.2.2.2)
  let B : ℝ × G → W := fun z => curveGraphLower (A z)
    (ambientCurveLower F e ρ z.1 (r z.2.1 + z.2.2.1) (deriv r z.2.1 + z.2.2.2))
    (deriv r z.2.1) (deriv (deriv r) z.2.1) (deriv (deriv (deriv r)) z.2.1)
    z.2.2.1 z.2.2.2
  change ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧ ∃ L_A L_B : NNReal,
    (∀ t ∈ Icc a b, ∀ z ∈ K, mu ≤ A (t, z) ∧ A (t, z) ≤ Lambda) ∧
    (∀ t ∈ Icc a b, LipschitzOnWith L_A (fun z => A (t, z)) K) ∧
    (∀ t ∈ Icc a b, LipschitzOnWith L_B (fun z => B (t, z)) K)
  have hΩ : IsOpen Ω := isOpen_curveGraphJetDomain F hV hρ hr
  obtain ⟨hA, hB, hpos⟩ := curveGraphCoefficients_contDiffOn F he hV hρ hr
  have hcompact : IsCompact (Icc a b ×ˢ K) := isCompact_Icc.prod hK
  have hKU : Icc a b ×ˢ K ⊆ Icc a b ×ˢ Ω := fun _ hz => ⟨hz.1, hsub hz.2⟩
  obtain ⟨L_A, hLA⟩ := exists_lipschitzOnWith_compact_product (convex_Icc a b) hΩ
    (hA.of_le (by simp)) hcompact hKU
  obtain ⟨L_B, hLB⟩ := exists_lipschitzOnWith_compact_product (convex_Icc a b) hΩ
    (hB.of_le (by simp)) hcompact hKU
  have hbounds : ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧
      ∀ z ∈ Icc a b ×ˢ K, mu ≤ A z ∧ A z ≤ Lambda := by
    by_cases hne : (Icc a b ×ˢ K).Nonempty
    · obtain ⟨zmin, hzmin, hmin⟩ := hcompact.exists_isMinOn hne (hA.mono hKU).continuousOn
      obtain ⟨zmax, hzmax, hmax⟩ := hcompact.exists_isMaxOn hne (hA.mono hKU).continuousOn
      exact ⟨A zmin, A zmax, hpos _ _ (hsub hzmin.2), hpos _ _ (hsub hzmax.2),
        fun _ hz => ⟨hmin hz, hmax hz⟩⟩
    · exact ⟨1, 1, zero_lt_one, zero_lt_one, fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨mu, Lambda, hmu, hLambda, hbounds⟩ := hbounds
  have hdist (t : ℝ) (z w : G) : dist (t, z) (t, w) = dist z w := by
    change max (dist t t) (dist z w) = dist z w
    simp only [dist_self, max_eq_right dist_nonneg]
  refine ⟨mu, Lambda, hmu, hLambda, L_A, L_B,
    (fun t ht z hz => hbounds (t, z) ⟨ht, hz⟩), ?_, ?_⟩
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hdist] using hLA.dist_le_mul (t, z) ⟨ht, hz⟩ (t, w) ⟨ht, hw⟩
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hdist] using hLB.dist_le_mul (t, z) ⟨ht, hz⟩ (t, w) ⟨ht, hw⟩

end PoincareConjecture.M63

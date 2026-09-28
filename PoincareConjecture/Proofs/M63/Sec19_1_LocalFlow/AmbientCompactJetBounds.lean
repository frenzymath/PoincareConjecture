import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCurveCoefficients
import PoincareConjecture.Proofs.M63.Mathlib.CompactProductLipschitz










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι




theorem isOpen_ambientCurveJetDomain (F : RicciFlow n M (Icc a b))
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) :
    IsOpen {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} := by
  obtain ⟨s, hs, _, _, _⟩ := F.nontrivial
  have ha : a ∈ Icc a b := ⟨le_rfl, hs.1.trans hs.2⟩
  let G : W × W → ℝ := fun z => (F.metric a).inner (ρ z.1)
    (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2) (mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2)
  have hparam : ContDiff ℝ ∞ (fun z : W × W => ((a, z.1), z.2)) := by fun_prop
  have hG : ContinuousOn G (U ×ˢ univ) :=
    ((flow_pullback_metric_hessian_contDiffOn F hU hρ
      (f := fun _ => 0) contMDiff_const).1.comp hparam.contDiffOn
        (fun _ hz => ⟨⟨ha, hz.1⟩, mem_univ _⟩)).continuousOn
  have heq : {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} =
      (U ×ˢ univ) ∩ G ⁻¹' Ioi 0 := by
    ext z
    refine ⟨fun hz => ⟨⟨hz.1, mem_univ _⟩, (F.metric a).pos (ρ z.1) _ hz.2⟩, ?_⟩
    intro hz
    refine ⟨hz.1.1, ?_⟩
    intro hzero
    have hpos : 0 < G z := hz.2
    simp only [G, hzero, map_zero] at hpos
    exact (lt_irrefl 0) hpos
  rw [heq]
  exact hG.isOpen_inter_preimage (hU.prod isOpen_univ) isOpen_Ioi





theorem ambientCurveCoefficients_uniform_bounds (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {K : Set (W × W)} (hK : IsCompact K)
    (hsub : K ⊆ {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}) :
    ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧ ∃ L_A L_B L_D : NNReal,
      (∀ t ∈ Icc a b, ∀ z ∈ K,
        mu ≤ ambientCurvePrincipal F ρ t z.1 z.2 ∧
          ambientCurvePrincipal F ρ t z.1 z.2 ≤ Lambda) ∧
      (∀ t ∈ Icc a b,
        LipschitzOnWith L_A (fun z : W × W => ambientCurvePrincipal F ρ t z.1 z.2) K) ∧
      (∀ t ∈ Icc a b,
        LipschitzOnWith L_B (fun z : W × W => ambientCurveLower F e ρ t z.1 z.2) K) ∧
      (∀ t ∈ Icc a b, LipschitzOnWith L_D (fun z : W × W =>
        retractionParabolicDefect (e ∘ ρ) (ambientCurvePrincipal F ρ)
          (ambientCurveLower F e ρ) t z.1 z.2) K) := by
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let A : ℝ × (W × W) → ℝ := fun z => ambientCurvePrincipal F ρ z.1 z.2.1 z.2.2
  let B : ℝ × (W × W) → W := fun z => ambientCurveLower F e ρ z.1 z.2.1 z.2.2
  let r : W → W := e ∘ ρ
  let D : ℝ × (W × W) → W := fun z =>
    retractionParabolicDefect r (ambientCurvePrincipal F ρ)
      (ambientCurveLower F e ρ) z.1 z.2.1 z.2.2
  have hΩ : IsOpen Ω := isOpen_ambientCurveJetDomain F hU hρ
  obtain ⟨hAraw, hBraw, hposraw⟩ := ambientCurveCoefficients_contDiffOn F he hU hρ
  have hparam : ContDiff ℝ ∞
      (fun z : ℝ × (W × W) => ((z.1, z.2.1), z.2.2)) := by fun_prop
  have hAcomp := hAraw.comp (s := Icc a b ×ˢ Ω) hparam.contDiffOn
    (fun _ hz => ⟨hz.1, hz.2⟩)
  have hA : ContDiffOn ℝ ∞ A (Icc a b ×ˢ Ω) := hAcomp
  have hBcomp := hBraw.comp (s := Icc a b ×ˢ Ω) hparam.contDiffOn
    (fun _ hz => ⟨hz.1, hz.2⟩)
  have hB : ContDiffOn ℝ ∞ B (Icc a b ×ˢ Ω) := hBcomp
  have hr : ContDiffOn ℝ ∞ r U := (he.comp_contMDiffOn hρ).contDiffOn
  have hDr : ContDiffOn ℝ ∞ (fderiv ℝ r) U := hr.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hDDr : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ r)) U :=
    hDr.fderiv_of_isOpen hU (m := ∞) (by simp)
  have hz : ContDiffOn ℝ ∞ (fun z : ℝ × (W × W) => z.2.1) (Icc a b ×ˢ Ω) :=
    contDiff_snd.fst.contDiffOn
  have hv : ContDiffOn ℝ ∞ (fun z : ℝ × (W × W) => z.2.2) (Icc a b ×ˢ Ω) :=
    contDiff_snd.snd.contDiffOn
  have hDrparam : ContDiffOn ℝ ∞ (fun z : ℝ × (W × W) => fderiv ℝ r z.2.1)
      (Icc a b ×ˢ Ω) := hDr.comp hz (fun _ hx => hx.2.1)
  have hDDrparam : ContDiffOn ℝ ∞
      (fun z : ℝ × (W × W) => fderiv ℝ (fderiv ℝ r) z.2.1) (Icc a b ×ˢ Ω) :=
    hDDr.comp hz (fun _ hx => hx.2.1)
  have hsecond : ContDiffOn ℝ ∞
      (fun z : ℝ × (W × W) => fderiv ℝ (fderiv ℝ r) z.2.1 z.2.2 z.2.2)
      (Icc a b ×ˢ Ω) := (hDDrparam.clm_apply hv).clm_apply hv
  have hD : ContDiffOn ℝ ∞ D (Icc a b ×ˢ Ω) :=
    ((hA.smul hsecond).add hB).sub (hDrparam.clm_apply hB)
  have hcompact : IsCompact (Icc a b ×ˢ K) := isCompact_Icc.prod hK
  have hKU : Icc a b ×ˢ K ⊆ Icc a b ×ˢ Ω := fun _ hz => ⟨hz.1, hsub hz.2⟩
  obtain ⟨L_A, hLA⟩ := exists_lipschitzOnWith_compact_product (convex_Icc a b) hΩ
    (hA.of_le (by simp)) hcompact hKU
  obtain ⟨L_B, hLB⟩ := exists_lipschitzOnWith_compact_product (convex_Icc a b) hΩ
    (hB.of_le (by simp)) hcompact hKU
  obtain ⟨L_D, hLD⟩ := exists_lipschitzOnWith_compact_product (convex_Icc a b) hΩ
    (hD.of_le (by simp)) hcompact hKU
  have hpos (z : ℝ × (W × W)) (hz : z ∈ Icc a b ×ˢ K) : 0 < A z :=
    hposraw z.1 z.2.1 (hsub hz.2).1 z.2.2 (hsub hz.2).2
  have hbounds : ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧
      ∀ z ∈ Icc a b ×ˢ K, mu ≤ A z ∧ A z ≤ Lambda := by
    by_cases hne : (Icc a b ×ˢ K).Nonempty
    · obtain ⟨zmin, hzmin, hmin⟩ := hcompact.exists_isMinOn hne (hA.mono hKU).continuousOn
      obtain ⟨zmax, hzmax, hmax⟩ := hcompact.exists_isMaxOn hne (hA.mono hKU).continuousOn
      exact ⟨A zmin, A zmax, hpos zmin hzmin, hpos zmax hzmax,
        fun _ hz => ⟨hmin hz, hmax hz⟩⟩
    · exact ⟨1, 1, zero_lt_one, zero_lt_one, fun z hz => (hne ⟨z, hz⟩).elim⟩
  obtain ⟨mu, Lambda, hmu, hLambda, hbounds⟩ := hbounds
  have hdist (t : ℝ) (z w : W × W) : dist (t, z) (t, w) = dist z w := by
    change max (dist t t) (dist z w) = dist z w
    simp only [dist_self, max_eq_right dist_nonneg]
  refine ⟨mu, Lambda, hmu, hLambda, L_A, L_B, L_D,
    (fun t ht z hz => hbounds (t, z) ⟨ht, hz⟩), ?_, ?_, ?_⟩
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hdist] using hLA.dist_le_mul (t, z) ⟨ht, hz⟩ (t, w) ⟨ht, hw⟩
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hdist] using hLB.dist_le_mul (t, z) ⟨ht, hz⟩ (t, w) ⟨ht, hw⟩
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [hdist] using hLD.dist_le_mul (t, z) ⟨ht, hz⟩ (t, w) ⟨ht, hw⟩

end PoincareConjecture.M63

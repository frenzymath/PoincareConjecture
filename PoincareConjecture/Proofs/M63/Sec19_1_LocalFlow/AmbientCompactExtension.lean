import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactJetBounds
import PoincareConjecture.Proofs.M63.Mathlib.FiniteOrderCompactExtension

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem exists_ambientCurve_compact_extension (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {K : Set (W × W)} (hK : IsCompact K)
    (hsub : K ⊆ {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    (k : ℕ) {tau : ℝ} (htau : 0 ≤ tau) (htaub : tau < b - a) :
    ∃ C : C(ℝ × (W × W), ℝ × W), ContDiff ℝ k C ∧ HasCompactSupport C ∧
      ∃ O : Set (ℝ × (W × W)), IsOpen O ∧ Icc 0 tau ×ˢ K ⊆ O ∧
        O ⊆ Iio (b - a) ×ˢ
          {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} ∧
        ∀ z ∈ O, 0 ≤ z.1 → C z =
          (1 - ambientCurvePrincipal F ρ (a + z.1) z.2.1 z.2.2,
            ambientCurveLower F e ρ (a + z.1) z.2.1 z.2.2) := by
  let Ω : Set (W × W) := {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  let f : ℝ × (W × W) → ℝ × W := fun z =>
    (1 - ambientCurvePrincipal F ρ (a + z.1) z.2.1 z.2.2,
      ambientCurveLower F e ρ (a + z.1) z.2.1 z.2.2)
  have hΩ : IsOpen Ω := isOpen_ambientCurveJetDomain F hU hρ
  obtain ⟨hAraw, hBraw, _⟩ := ambientCurveCoefficients_contDiffOn F he hU hρ
  have hparam : ContDiff ℝ ∞
      (fun z : ℝ × (W × W) => ((a + z.1, z.2.1), z.2.2)) := by fun_prop
  have hmaps : MapsTo (fun z : ℝ × (W × W) => ((a + z.1, z.2.1), z.2.2))
      (Ico 0 (b - a) ×ˢ Ω)
      {z : (ℝ × W) × W | z.1.1 ∈ Icc a b ∧ z.1.2 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2 ≠ 0} := by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hA := hAraw.comp (s := Ico 0 (b - a) ×ˢ Ω) hparam.contDiffOn hmaps
  have hB := hBraw.comp (s := Ico 0 (b - a) ×ˢ Ω) hparam.contDiffOn hmaps
  have hf : ContDiffOn ℝ ∞ f (Ico 0 (b - a) ×ˢ Ω) :=
    (contDiffOn_const.sub hA).prodMk hB
  obtain ⟨C, hC, hCc, O, hO, hKO, hOU, heq⟩ :=
    exists_finiteOrder_initialSlab_extension k hΩ hK hsub (htau.trans_lt htaub)
      htau htaub f (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k))
  exact ⟨C, hC, hCc, O, hO, hKO, hOU,
    fun z hz ht => heq ⟨hz, ht, mem_univ _⟩⟩

end PoincareConjecture.M63

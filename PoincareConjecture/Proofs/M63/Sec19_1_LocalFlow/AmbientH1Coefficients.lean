import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactExtension
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CompactTameH1Coefficients

set_option autoImplicit false

open Set PoincareConjecture.SpectralHeatNative
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)

theorem exists_ambientCurveH1_coefficients (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {K : Set (W × W)} (hK : IsCompact K)
    (hsub : K ⊆ {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    {tau : ℝ} (htau : 0 ≤ tau) (htaub : tau < b - a) :
    let jet := fun (u : S) (x : AddCircle L) =>
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x))
    ∃ O : Set (ℝ × (W × W)), IsOpen O ∧ Icc 0 tau ×ˢ K ⊆ O ∧
      O ⊆ Iio (b - a) ×ˢ
        {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} ∧
      ∃ (G : ℝ × S → lp (fun _ : ℤ => ℂ) 2) (Q : ℝ × S → S),
        ContDiff ℝ 1 G ∧ ContDiff ℝ 1 Q ∧
        (∀ t u x, (t, jet u x) ∈ O → 0 ≤ t →
          periodicSobolevJet (L := L) 0 0 (by omega) (G (t, u)) x =
            ((1 - ambientCurvePrincipal F ρ (a + t) (jet u x).1 (jet u x).2 : ℝ) : ℂ) ∧
          ∀ i, periodicSobolevJet (L := L) 0 0 (by omega)
              (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (Q (t, u)) i)) x =
            (ambientCurveLower F e ρ (a + t) (jet u x).1 (jet u x).2 i : ℂ)) ∧
        ∀ R : ℝ, 0 ≤ R → ∃ KG KQ : NNReal, ∀ t u v, ‖u‖ ≤ R → ‖v‖ ≤ R →
          ‖G (t, u) - G (t, v)‖ ≤ KG * ‖u - v‖ ∧
          ‖Q (t, u) - Q (t, v)‖ ≤ KQ * ‖u - v‖ := by
  classical
  dsimp only
  obtain ⟨C, hC, hCc, O, hO, hKO, hOU, heq⟩ :=
    exists_ambientCurve_compact_extension F he hU hρ hK hsub 2 htau htaub
  let J := Fin 2 × ι
  let E : W ≃L[ℝ] (ι → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let R (j : Fin 2) : (J → ℝ) →L[ℝ] W := E.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (j, i)))
  let D : (ℝ × (J → ℝ)) →L[ℝ] ℝ × (W × W) :=
    (ContinuousLinearMap.fst ℝ ℝ (J → ℝ)).prod
      (((R 0).prod (R 1)).comp (ContinuousLinearMap.snd ℝ ℝ (J → ℝ)))
  have hDinj : Function.Injective D := by
    intro p q hpq
    apply Prod.ext
    · exact congrArg (fun z : ℝ × (W × W) => z.1) hpq
    · funext j
      rcases j with ⟨j, i⟩
      fin_cases j
      · exact congrArg (fun z : ℝ × (W × W) => z.2.1 i) hpq
      · exact congrArg (fun z : ℝ × (W × W) => z.2.2 i) hpq
  have hDc : Topology.IsClosedEmbedding D :=
    LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hDinj)
  have hCD := hC.comp D.contDiff
  have hCDc := hCc.comp_isClosedEmbedding hDc
  let f : ℝ × (J → ℝ) → ℝ := fun z => (C (D z)).1
  let g : ℝ × (J → ℝ) → (ι → ℝ) := fun z => E (C (D z)).2
  have hf := hCD.fst
  have hg := E.contDiff.comp hCD.snd
  have hfc := hCDc.comp_left (g := (Prod.fst : ℝ × W → ℝ)) rfl
  have hgc := hCDc.comp_left (g := fun z : ℝ × W => E z.2) (map_zero E)
  obtain ⟨G, hG, hGdecode, hGlip⟩ := exists_compact_scalarH1_coefficient (L := L) f hf hfc
  obtain ⟨Q, hQ, hQdecode, hQlip⟩ := exists_compact_vectorH1_coefficient (L := L) g hg hgc
  refine ⟨O, hO, hKO, hOU, G, Q, hG, hQ, ?_, ?_⟩
  · intro t u x hx ht
    constructor
    · rw [hGdecode]
      change ((C (t, (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x)))).1 : ℂ) = _
      rw [heq _ hx ht]
    · intro i
      rw [hQdecode]
      change ((C (t, (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x)))).2 i : ℂ) = _
      rw [heq _ hx ht]
  · intro R hR
    obtain ⟨KG, hKG⟩ := hGlip R hR
    obtain ⟨KQ, hKQ⟩ := hQlip R hR
    exact ⟨KG, KQ, fun t u v hu hv => ⟨hKG t u v hu hv, hKQ t u v hu hv⟩⟩

end PoincareConjecture.M63

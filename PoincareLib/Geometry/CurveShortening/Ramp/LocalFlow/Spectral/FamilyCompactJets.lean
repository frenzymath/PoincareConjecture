import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Ambient.CompactJetBounds
import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.Vector.PeriodicJets
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# One compact immersed jet domain for a spectral family

The actual jet image of a convergent sequence of compact paths is
compact. Its literal immersion guards give uniform ellipticity and
coefficient bounds. MT2007 Claim 19.1, p. 437;
`2026-09-22-spectral-family-compact-jets.md`.
-/

set_option autoImplicit false

open Set Filter PoincareMT.SpectralHeatNative
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]
  {Z : Type w} [TopologicalSpace Z] [CompactSpace Z]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)

/-- The whole convergent spectral family has one compact immersed jet
domain with actual coefficient bounds uniform through both ambient time
endpoints. MT2007 Claim 19.1, p. 437; compact spectral jets derivation. -/
theorem exists_compact_spectral_family_jet_domain
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    (Vn : ℕ → C(Z, S)) (V : C(Z, S))
    (hV : Tendsto Vn atTop (𝓝 V)) :
    let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
    let jet := fun (v : S) (x : AddCircle L) =>
      (E (vectorPeriodicJet (L := L) 1 0 (by omega) v x),
        E (vectorPeriodicJet (L := L) 1 1 (by omega) v x))
    let Ω : Set (W × W) :=
      {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
    (∀ j z x, jet (Vn j z) x ∈ Ω) →
    (∀ z x, jet (V z) x ∈ Ω) →
    ∃ K : Set (W × W), IsCompact K ∧ K ⊆ Ω ∧
      (∀ z x, jet (V z) x ∈ K) ∧
      (∀ j z x, jet (Vn j z) x ∈ K) ∧
      ∃ mu Lambda : ℝ, 0 < mu ∧ 0 < Lambda ∧
        ∃ L_A L_B L_D : NNReal,
          (∀ t ∈ Icc a b, ∀ z ∈ K,
            mu ≤ ambientCurvePrincipal F ρ t z.1 z.2 ∧
              ambientCurvePrincipal F ρ t z.1 z.2 ≤ Lambda) ∧
          (∀ t ∈ Icc a b, LipschitzOnWith L_A
            (fun z : W × W => ambientCurvePrincipal F ρ t z.1 z.2) K) ∧
          (∀ t ∈ Icc a b, LipschitzOnWith L_B
            (fun z : W × W => ambientCurveLower F e ρ t z.1 z.2) K) ∧
          (∀ t ∈ Icc a b, LipschitzOnWith L_D (fun z : W × W =>
            retractionParabolicDefect (e ∘ ρ) (ambientCurvePrincipal F ρ)
              (ambientCurveLower F e ρ) t z.1 z.2) K) := by
  classical
  dsimp only
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let jet := fun (v : S) (x : AddCircle L) =>
    (E (vectorPeriodicJet (L := L) 1 0 (by omega) v x),
      E (vectorPeriodicJet (L := L) 1 1 (by omega) v x))
  let Ω : Set (W × W) :=
    {z | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0}
  intro hguardn hguard
  let P : Set C(Z, S) := insert V (range Vn)
  let A : Set ((C(Z, S) × Z) × AddCircle L) := (P ×ˢ univ) ×ˢ univ
  let J : (C(Z, S) × Z) × AddCircle L → W × W :=
    fun z => jet (z.1.1 z.1.2) z.2
  have heval : Continuous (fun z : (C(Z, S) × Z) × AddCircle L => z.1.1 z.1.2) :=
    continuous_eval.comp continuous_fst
  have hD0 : Continuous (fun z : (C(Z, S) × Z) × AddCircle L =>
      vectorPeriodicJet (L := L) 1 0 (by omega) (z.1.1 z.1.2)) :=
    (vectorPeriodicJet (L := L) 1 0 (by omega)).continuous.comp heval
  have hD1 : Continuous (fun z : (C(Z, S) × Z) × AddCircle L =>
      vectorPeriodicJet (L := L) 1 1 (by omega) (z.1.1 z.1.2)) :=
    (vectorPeriodicJet (L := L) 1 1 (by omega)).continuous.comp heval
  have hJ : Continuous J :=
    (E.continuous.comp (continuous_eval.comp (hD0.prodMk continuous_snd))).prodMk
      (E.continuous.comp (continuous_eval.comp (hD1.prodMk continuous_snd)))
  have hA : IsCompact A := (hV.isCompact_insert_range.prod isCompact_univ).prod isCompact_univ
  let K := J '' A
  have hK : IsCompact K := hA.image hJ
  have hsub : K ⊆ Ω := by
    rintro q ⟨⟨⟨v, z⟩, x⟩, hv, rfl⟩
    rcases hv.1.1 with rfl | ⟨j, rfl⟩
    · exact hguard z x
    · exact hguardn j z x
  refine ⟨K, hK, hsub, ?_, ?_, ambientCurveCoefficients_uniform_bounds F he hU hρ hK hsub⟩
  · intro z x
    exact ⟨((V, z), x), ⟨⟨mem_insert _ _, mem_univ _⟩, mem_univ _⟩, rfl⟩
  · intro j z x
    exact ⟨((Vn j, z), x),
      ⟨⟨mem_insert_of_mem _ (mem_range_self j), mem_univ _⟩, mem_univ _⟩, rfl⟩

end PoincareMT.M63

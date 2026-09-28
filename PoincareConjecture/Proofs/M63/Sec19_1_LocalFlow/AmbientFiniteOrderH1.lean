import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCompactExtension
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.TimeParameterH1Composition









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





theorem exists_ambientCurveH1_finite_coefficients (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {K : Set (W × W)} (hK : IsCompact K)
    (hsub : K ⊆ {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    (k : ℕ) {tau : ℝ} (htau : 0 ≤ tau) (htaub : tau < b - a) :
    let jet := fun (u : S) (x : AddCircle L) =>
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x))
    ∃ O : Set (ℝ × (W × W)), IsOpen O ∧ Icc 0 tau ×ˢ K ⊆ O ∧
      O ⊆ Iio (b - a) ×ˢ
        {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0} ∧
      ∃ (G : ℝ × S → lp (fun _ : ℤ => ℂ) 2) (Q : ℝ × S → S),
        ContDiff ℝ k G ∧ ContDiff ℝ k Q ∧
        ∀ t u x, (t, jet u x) ∈ O → 0 ≤ t →
          periodicSobolevJet (L := L) 0 0 (by omega) (G (t, u)) x =
            ((1 - ambientCurvePrincipal F ρ (a + t) (jet u x).1 (jet u x).2 : ℝ) : ℂ) ∧
          ∀ i, periodicSobolevJet (L := L) 0 0 (by omega)
              (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (Q (t, u)) i)) x =
            (ambientCurveLower F e ρ (a + t) (jet u x).1 (jet u x).2 i : ℂ) := by
  classical
  dsimp only
  obtain ⟨C, hC, _hCc, O, hO, hKO, hOU, heq⟩ :=
    exists_ambientCurve_compact_extension F he hU hρ hK hsub (k + 1) htau htaub
  let J := Fin 2 × ι
  let E : W ≃L[ℝ] (ι → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)
  let R (j : Fin 2) : (J → ℝ) →L[ℝ] W := E.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (j, i)))
  let D : (ℝ × (J → ℝ)) →L[ℝ] ℝ × (W × W) :=
    (ContinuousLinearMap.fst ℝ ℝ (J → ℝ)).prod
      (((R 0).prod (R 1)).comp (ContinuousLinearMap.snd ℝ ℝ (J → ℝ)))
  have hCD := hC.comp D.contDiff
  let f : ℝ × (J → ℝ) → ℝ := fun z => (C (D z)).1
  let g : ℝ × (J → ℝ) → (ι → ℝ) := fun z => E (C (D z)).2
  obtain ⟨G, hG, hGdecode⟩ :=
    exists_timeParameter_scalarH1_composition (L := L) k f hCD.fst
  obtain ⟨Q, hQ, hQdecode⟩ :=
    exists_timeParameter_vectorH1_composition (L := L) k g (E.contDiff.comp hCD.snd)
  refine ⟨O, hO, hKO, hOU, G, Q, hG, hQ, ?_⟩
  intro t u x hx ht
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

end PoincareConjecture.M63

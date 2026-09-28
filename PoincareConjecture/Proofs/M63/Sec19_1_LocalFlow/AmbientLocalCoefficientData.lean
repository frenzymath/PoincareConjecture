import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientH1Coefficients
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientFiniteOrderH1
import Mathlib.Topology.CompactOpen

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

theorem exists_ambient_local_coefficient_data (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {K : Set (W × W)} (hK : IsCompact K)
    (hsub : K ⊆ {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    (w : S) {tau : ℝ} (htau : 0 < tau) (htaub : tau < b - a) :
    let jet := fun (u : S) (x : AddCircle L) =>
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x))
    (∀ x, jet w x ∈ K) →
    (∀ x, ambientCurvePrincipal F ρ a (jet w x).1 (jet w x).2 = 1) →
    ∃ O : Set (ℝ × S), IsOpen O ∧ (0, w) ∈ O ∧
      (∀ z ∈ O, z.1 < tau ∧ ∀ x, (jet z.2 x).1 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (jet z.2 x).1 (jet z.2 x).2 ≠ 0) ∧
      ∃ (G : ℝ × S → lp (fun _ : ℤ => ℂ) 2) (Q : ℝ × S → S),
        ContDiff ℝ 1 G ∧ ContDiff ℝ 1 Q ∧ G (0, w) = 0 ∧
        (∀ R : ℝ, 0 ≤ R → ∃ KG KQ : NNReal, ∀ t u v, ‖u‖ ≤ R → ‖v‖ ≤ R →
          ‖G (t, u) - G (t, v)‖ ≤ KG * ‖u - v‖ ∧
          ‖Q (t, u) - Q (t, v)‖ ≤ KQ * ‖u - v‖) ∧
        (∀ t u, 0 ≤ t → (t, u) ∈ O → ∀ x,
          periodicSobolevJet (L := L) 0 0 (by omega) (G (t, u)) x =
            ((1 - ambientCurvePrincipal F ρ (a + t) (jet u x).1 (jet u x).2 : ℝ) : ℂ) ∧
          ∀ i, periodicSobolevJet (L := L) 0 0 (by omega)
              (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (Q (t, u)) i)) x =
            (ambientCurveLower F e ρ (a + t) (jet u x).1 (jet u x).2 i : ℂ)) ∧
        ∀ k : ℕ, ∃ (Gk : ℝ × S → lp (fun _ : ℤ => ℂ) 2) (Qk : ℝ × S → S),
          ContDiff ℝ k Gk ∧ ContDiff ℝ k Qk ∧
          ∀ t u, 0 ≤ t → (t, u) ∈ O → G (t, u) = Gk (t, u) ∧ Q (t, u) = Qk (t, u) := by
  classical
  dsimp only
  intro hjet hunit
  let jet := fun (u : S) (x : AddCircle L) =>
    (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x),
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x))
  obtain ⟨K', hK', hKK', hK'U⟩ :=
    exists_compact_between hK (isOpen_ambientCurveJetDomain F hU hρ) hsub
  let E : (ι → ℝ) ≃L[ℝ] W :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let D0 : S →L[ℝ] C(AddCircle L, W) :=
    (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 0 (by omega))
  let D1 : S →L[ℝ] C(AddCircle L, W) :=
    (E.toContinuousLinearMap.compLeftContinuous ℝ (AddCircle L)).comp
      (vectorPeriodicJet (L := L) 1 1 (by omega))
  let D : S → C(AddCircle L, W × W) := fun u => (D0 u).prodMk (D1 u)
  have hD : Continuous D := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_eval.comp ((D0.continuous.comp continuous_fst).prodMk continuous_snd)).prodMk
      (continuous_eval.comp ((D1.continuous.comp continuous_fst).prodMk continuous_snd))
  let H : ℝ × S → C(AddCircle L, ℝ × (W × W)) := fun z =>
    (ContinuousMap.const (AddCircle L) z.1).prodMk (D z.2)
  have hH : Continuous H := ContinuousMap.continuous_prodMk_const.comp
    (continuous_fst.prodMk (hD.comp continuous_snd))
  let O : Set (ℝ × S) := {z | ∀ x, (z.1, jet z.2 x) ∈ Iio tau ×ˢ interior K'}
  have hO : IsOpen O := by
    have heq : O = H ⁻¹' {f : C(AddCircle L, ℝ × (W × W)) |
        MapsTo f univ (Iio tau ×ˢ interior K')} := by
      ext z
      exact ⟨fun hz x _ => hz x, fun hz x => hz (mem_univ x)⟩
    rw [heq]
    exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_univ
      (isOpen_Iio.prod isOpen_interior)).preimage hH
  have hw : (0, w) ∈ O := fun x => ⟨htau, hKK' (hjet x)⟩
  have hcylinder (t : ℝ) (u : S) (ht : 0 ≤ t) (hu : (t, u) ∈ O) (x : AddCircle L) :
      (t, jet u x) ∈ Icc 0 tau ×ˢ K' :=
    ⟨⟨ht, (hu x).1.le⟩, interior_subset (hu x).2⟩
  obtain ⟨O1, _hO1, hK1, _hO1U, G, Q, hG, hQ, hdecode, hLip⟩ :=
    exists_ambientCurveH1_coefficients (L := L) F he hU hρ hK' hK'U htau.le htaub
  have hdecodeO (t : ℝ) (u : S) (ht : 0 ≤ t) (hu : (t, u) ∈ O) (x : AddCircle L) :=
    hdecode t u x (hK1 (hcylinder t u ht hu x)) ht
  have hGzero : G (0, w) = 0 := by
    apply periodicH1Decoder_injective (L := L)
    apply ContinuousMap.ext
    intro x
    rw [map_zero, ContinuousMap.zero_apply]
    simpa only [add_zero, hunit x, sub_self, Complex.ofReal_zero] using
      (hdecodeO 0 w le_rfl hw x).1
  refine ⟨O, hO, hw, ?_, G, Q, hG, hQ, hGzero, hLip, hdecodeO, ?_⟩
  · intro z hz
    exact ⟨(hz 0).1, fun x => hK'U (interior_subset (hz x).2)⟩
  · intro k
    obtain ⟨Ok, _hOk, hKk, _hOkU, Gk, Qk, hGk, hQk, hdecodek⟩ :=
      exists_ambientCurveH1_finite_coefficients (L := L) F he hU hρ hK' hK'U k htau.le htaub
    refine ⟨Gk, Qk, hGk, hQk, ?_⟩
    intro t u ht hu
    constructor
    · apply periodicH1Decoder_injective (L := L)
      apply ContinuousMap.ext
      intro x
      exact (hdecodeO t u ht hu x).1.trans
        (hdecodek t u x (hKk (hcylinder t u ht hu x)) ht).1.symm
    · apply (lpFinitePiEquiv (α := ℤ × Fin 2) (ι := ι) (E := ℝ) ℝ).injective
      funext i
      apply complexLpRealEquiv.symm.injective
      apply periodicH1Decoder_injective (L := L)
      apply ContinuousMap.ext
      intro x
      exact ((hdecodeO t u ht hu x).2 i).trans
        ((hdecodek t u x (hKk (hcylinder t u ht hu x)) ht).2 i).symm

end PoincareConjecture.M63

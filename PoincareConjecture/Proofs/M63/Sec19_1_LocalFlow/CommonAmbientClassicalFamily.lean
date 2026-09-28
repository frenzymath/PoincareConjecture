import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CommonAmbientSpectralFamily











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)





theorem exists_common_ambient_classical_family (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {K : Set (W × W)} (hK : IsCompact K)
    (hsub : K ⊆ {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    (w : S) {Tcap : ℝ} (hTcap : 0 < Tcap) (hTcapb : Tcap < b - a) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    let jet := fun (z : S) (x : AddCircle L) =>
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
    (∀ x, jet w x ∈ K) →
    (∀ x, ambientCurvePrincipal F ρ a (jet w x).1 (jet w x).2 = 1) →
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ Tcap ∧ T ≤ 1 ∧
      ∃ (B : Set S) (u : S → ForcingSpace ((ℤ × Fin 2) × ι) T),
        IsOpen B ∧ w ∈ B ∧
        ContDiffOn ℝ ∞ (fun z => initialResponseTrace lambda z hT.le (u z)) B ∧
        let q := fun z => initialResponseCurve (L := L) hT.le z (u z)
        ContinuousOn (fun z : S × (ℝ × ℝ) => q z.1 z.2.1 z.2.2) (B ×ˢ univ) ∧
        ContinuousOn (fun z : S × (ℝ × ℝ) => deriv (q z.1 z.2.1) z.2.2) (B ×ˢ univ) ∧
        (∀ z ∈ B, ∀ t, Function.Periodic (q z t) L) ∧
        (∀ z ∈ B, ∀ x : ℝ, q z 0 x = (jet z (x : AddCircle L)).1) ∧
        (∀ z ∈ B, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
          q z t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q z t x) (deriv (q z t) x) ≠ 0) ∧
        ∀ z ∈ B,
          ContDiffAt ℝ ∞ (fun s : ℝ => vectorPeriodicSpectralTranslation (L := L) s z) 0 →
          ContDiffOn ℝ ∞ (Function.uncurry (q z)) (Icc (0 : ℝ) T ×ˢ univ) ∧
          (∀ t ∈ Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => q z s x)
            (ambientCurvePrincipal F ρ (a + t) (q z t x) (deriv (q z t) x) •
                iteratedDeriv 2 (q z t) x +
              ambientCurveLower F e ρ (a + t) (q z t x) (deriv (q z t) x)) t) ∧
          ((∀ x, q z 0 x = e (ρ (q z 0 x))) →
            ∀ t ∈ Icc (0 : ℝ) T, ∀ x, q z t x = e (ρ (q z t x))) := by
  dsimp only
  intro hjet hunit
  obtain ⟨T, hT, hTTcap, hT1, B, u, hB, hwB, hpath,
      hq, hqx, hperiod, hzero, hguard, hsmooth⟩ :=
    exists_common_ambient_spectral_family F he hU heU hρ hρe hK hsub w hTcap hTcapb
      hjet hunit
  refine ⟨T, hT, hTTcap, hT1, B, u, hB, hwB, hpath,
    hq, hqx, hperiod, hzero, hguard, ?_⟩
  intro z hz hphase
  obtain ⟨hclosed, _horbit, hpde, hfixed⟩ := hsmooth z hz hphase
  exact ⟨hclosed, hpde, hfixed⟩

end PoincareConjecture.M63

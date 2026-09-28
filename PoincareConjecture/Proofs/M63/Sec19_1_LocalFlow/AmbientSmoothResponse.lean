import PoincareConjecture.Proofs.M63.Mathlib.CountableHilbertBasis
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientLocalCoefficientData
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SmoothCoefficientResponse
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialBranchTranslation
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.LocalizedCorrectedSource










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)





theorem exists_ambient_smooth_response (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    {K : Set (W × W)} (hK : IsCompact K)
    (hsub : K ⊆ {z : W × W | z.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1 z.2 ≠ 0})
    (w : S) {Tcap : ℝ} (hTcap : 0 < Tcap) (hTcapb : Tcap < b - a) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    let jet := fun (u : S) (x : AddCircle L) =>
      (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x),
        WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x))
    (∀ x, jet w x ∈ K) →
    (∀ x, ambientCurvePrincipal F ρ a (jet w x).1 (jet w x).2 = 1) →
    ∃ T : ℝ, ∃ hT : 0 < T, T ≤ Tcap ∧ T ≤ 1 ∧
      ∃ (F0 : ForcingSpace ((ℤ × Fin 2) × ι) T) (u : S → ForcingSpace ((ℤ × Fin 2) × ι) T),
        u w = F0 ∧ ContDiffAt ℝ ∞ u w ∧
        ContDiffAt ℝ ∞ (fun w' => initialResponseTrace lambda w' hT.le (u w')) w ∧
        (∀ᶠ s : ℝ in 𝓝 0,
          u (vectorPeriodicSpectralTranslation (L := L) s w) =
            (vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F0) ∧
        (∀ t : Icc (0 : ℝ) T, ∀ x, let j := jet (initialResponseTrace lambda w hT.le F0 t) x
          j.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ j.1 j.2 ≠ 0) ∧
        ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ x i,
          let j := jet (initialResponseTrace lambda w hT.le F0 ⟨t, ht⟩) x
          vectorPeriodicJet (L := L) 0 0 (by omega) (F0 t) x i =
            (ambientCurvePrincipal F ρ (a + t) j.1 j.2 - 1) *
              vectorPeriodicJet (L := L) 2 2 (by omega)
                (initialHeatHigh lambda w t + shiftedHighOperator hT.le lambda F0 t) x i +
              ambientCurveLower F e ρ (a + t) j.1 j.2 i := by
  classical
  dsimp only
  intro hjet hunit
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let jet := fun (v : S) (x : AddCircle L) =>
    (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) v x),
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) v x))
  obtain ⟨O, hO, hw, hOU, G, Q, hG, hQ, hzero, hLip, hdecode, hext⟩ :=
    exists_ambient_local_coefficient_data (L := L) F he hU hρ hK hsub w hTcap hTcapb
      hjet hunit
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : SecondCountableTopology (lp (fun _ : ℤ => ℂ) 2) :=
    secondCountable_of_countable_hilbertBasis
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℤ => ℂ) 2)))
  obtain ⟨Bmul, hcomplex, _hBnorm, hreal⟩ := exists_vectorPeriodicH1_product (L := L) (ι := ι)
  obtain ⟨T, hT, hTTcap, hT1, F0, u, _hFcap, huw, hu, hpath, heq, hunique,
      hinside, _htraceBound⟩ :=
    exists_smooth_coefficient_parameter_response lambda w hTcap (rcap := 1) zero_lt_one
      Bmul G Q hG hQ hzero hLip hO hw hext
  have hM := vectorPeriodicH1_product_spectralTranslation Bmul hcomplex
  let coord : ((Fin 2 × ι) → ℝ) → W × W := fun j =>
    (WithLp.toLp 2 (fun i => j (0, i)), WithLp.toLp 2 (fun i => j (1, i)))
  let g := fun t j => 1 - ambientCurvePrincipal F ρ (a + t) (coord j).1 (coord j).2
  let q := fun t j i => ambientCurveLower F e ρ (a + t) (coord j).1 (coord j).2 i
  have hdecode' (t : ℝ) (v : S) (ht : 0 ≤ t) (hv : (t, v) ∈ O) (x : AddCircle L) :
      periodicSobolevJet (L := L) 0 0 (by omega) (G (t, v)) x =
        (g t (fun j => vectorPeriodicJet (L := L) 1 j.1 (by omega) v x j.2) : ℂ) ∧
      ∀ i, periodicSobolevJet (L := L) 0 0 (by omega)
          (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (Q (t, v)) i)) x =
        (q t (fun j => vectorPeriodicJet (L := L) 1 j.1 (by omega) v x j.2) i : ℂ) :=
    hdecode t v ht hv x
  have hcoeff := fun s t v ht hv hsv =>
    local_periodicH1_coefficients_spectralTranslation G Q g q hdecode' s
      (t := t) (u := v) ht hv hsv
  have heq0 := heq.self_of_nhds
  rw [huw] at heq0
  have hbranch := eventually_initialBranch_spectralTranslation Bmul G Q hM hO hcoeff
    hT.le w F0 u heq0 hunique hinside
  refine ⟨T, hT, hTTcap, hT1, F0, u, huw, hu, hpath, hbranch, ?_, ?_⟩
  · intro t x
    exact (hOU _ (hinside t)).2 x
  · filter_upwards [heq0, (initialResponseTrace_spec lambda w hT.le F0).2.2.2]
      with t hsource hhigh
    intro ht x i
    let V := initialResponseTrace lambda w hT.le F0 ⟨t, ht⟩
    let H := initialHeatHigh lambda w t + shiftedHighOperator hT.le lambda F0 t
    have hlocal := vectorPeriodic_correctedSource_at_trace (L := L)
      H V (Q (t, V)) (G (t, V))
      (fun x => ambientCurvePrincipal F ρ (a + t) (jet V x).1 (jet V x).2)
      (fun x => ambientCurveLower F e ρ (a + t) (jet V x).1 (jet V x).2)
      Bmul (hhigh ht)
      (fun x => (hdecode t V ht.1 (hinside ⟨t, ht⟩) x).1)
      (fun x i => (hdecode t V ht.1 (hinside ⟨t, ht⟩) x).2 i) hreal x i
    rw [hsource ht]
    exact hlocal

end PoincareConjecture.M63

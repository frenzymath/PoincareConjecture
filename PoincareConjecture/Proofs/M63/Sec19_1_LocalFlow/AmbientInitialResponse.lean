import PoincareConjecture.Proofs.M63.Mathlib.CountableHilbertBasis
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientH1Coefficients
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.CoefficientParameterResponse
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.InitialTraceNeighborhood
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.LocalizedCorrectedSource

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative QuasilinearDeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)

theorem exists_ambient_initial_response (F : RicciFlow n M (Icc a b))
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
        u w = F0 ∧ ContDiffAt ℝ 1 u w ∧
        ContDiffAt ℝ 1 (fun w' => initialResponseTrace lambda w' hT.le (u w')) w ∧
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
  let jet := fun (u : S) (x : AddCircle L) =>
    (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) u x),
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) u x))
  obtain ⟨O, hO, hKO, hOU, G, Q, hG, hQ, hdecode, hLip⟩ :=
    exists_ambientCurveH1_coefficients (L := L) F he hU hρ hK hsub hTcap.le hTcapb
  have hGzero : G (0, w) = 0 := by
    apply periodicH1Decoder_injective (L := L)
    apply ContinuousMap.ext
    intro x
    have h := (hdecode 0 w x (hKO ⟨⟨le_rfl, hTcap.le⟩, hjet x⟩) le_rfl).1
    rw [map_zero, ContinuousMap.zero_apply]
    simpa only [add_zero, hunit x, sub_self, Complex.ofReal_zero] using h
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
  have hDval (u : S) (x : AddCircle L) : D u x = jet u x := rfl
  obtain ⟨r0, hr0, T0, hT0, hT0cap, _hT01, hdomain⟩ :=
    exists_initialResponseTrace_neighborhood lambda w D hD hO
      (fun x => hKO ⟨⟨le_rfl, hTcap.le⟩, hjet x⟩) hTcap
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : SecondCountableTopology (lp (fun _ : ℤ => ℂ) 2) :=
    secondCountable_of_countable_hilbertBasis
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℤ => ℂ) 2)))
  obtain ⟨Bmul, _hcomplex, _hBnorm, hBmul⟩ := exists_vectorPeriodicH1_product (L := L) (ι := ι)
  obtain ⟨T, hT, hTT0, hT1, F0, u, hFcap, huw, hu, hpath, heq, _htraceBound⟩ :=
    exists_coefficient_parameter_response lambda w hT0 hr0 (k := 1) (by norm_num)
      Bmul G Q hG hQ hGzero hLip
  have hinside (t : Icc (0 : ℝ) T) (x : AddCircle L) :
      ((t : ℝ), jet (initialResponseTrace lambda w hT.le F0 t) x) ∈ O := by
    rw [← hDval]
    exact hdomain T hT.le hTT0 F0 hFcap t x
  refine ⟨T, hT, hTT0.trans hT0cap, hT1, F0, u, huw, hu, hpath,
    fun t x => (hOU (hinside t x)).2, ?_⟩
  have heq0 := heq.self_of_nhds
  rw [huw] at heq0
  filter_upwards [heq0, (initialResponseTrace_spec lambda w hT.le F0).2.2.2]
    with t hsource hhigh
  intro ht x i
  let V := initialResponseTrace lambda w hT.le F0 ⟨t, ht⟩
  let H := initialHeatHigh lambda w t + shiftedHighOperator hT.le lambda F0 t
  have hlocal := vectorPeriodic_correctedSource_at_trace (L := L)
    H V (Q (t, V)) (G (t, V))
    (fun x => ambientCurvePrincipal F ρ (a + t) (jet V x).1 (jet V x).2)
    (fun x => ambientCurveLower F e ρ (a + t) (jet V x).1 (jet V x).2)
    Bmul (hhigh ht)
    (fun x => (hdecode t V x (hinside ⟨t, ht⟩ x) ht.1).1)
    (fun x i => (hdecode t V x (hinside ⟨t, ht⟩ x) ht.1).2 i) hBmul x i
  rw [hsource ht]
  exact hlocal

end PoincareConjecture.M63

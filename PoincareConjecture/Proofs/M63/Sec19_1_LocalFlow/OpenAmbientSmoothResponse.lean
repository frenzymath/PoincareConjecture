import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientSmoothResponse
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.OpenSmoothCoefficientResponse










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





theorem exists_open_ambient_smooth_response (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
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
      ∃ (F0 : ForcingSpace ((ℤ × Fin 2) × ι) T)
        (u : S → ForcingSpace ((ℤ × Fin 2) × ι) T) (B : Set S),
        IsOpen B ∧ w ∈ B ∧ u w = F0 ∧ ContDiffOn ℝ ∞ u B ∧
        ContDiffOn ℝ ∞ (fun z => initialResponseTrace lambda z hT.le (u z)) B ∧
        (∀ z ∈ B, ∀ᶠ s : ℝ in 𝓝 0,
          u (vectorPeriodicSpectralTranslation (L := L) s z) =
            (vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) (u z)) ∧
        (∀ z ∈ B, ∀ t : Icc (0 : ℝ) T, ∀ x,
          let j := jet (initialResponseTrace lambda z hT.le (u z) t) x
          j.1 ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ j.1 j.2 ≠ 0) ∧
        ∀ z ∈ B, ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ x i,
          let j := jet (initialResponseTrace lambda z hT.le (u z) ⟨t, ht⟩) x
          vectorPeriodicJet (L := L) 0 0 (by omega) (u z t) x i =
            (ambientCurvePrincipal F ρ (a + t) j.1 j.2 - 1) *
              vectorPeriodicJet (L := L) 2 2 (by omega)
                (initialHeatHigh lambda z t + shiftedHighOperator hT.le lambda (u z) t) x i +
              ambientCurveLower F e ρ (a + t) j.1 j.2 i := by
  classical
  dsimp only
  intro hjet hunit
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let jet := fun (z : S) (x : AddCircle L) =>
    (WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) z x),
      WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) z x))
  obtain ⟨O, hO, hw, hOU, G, Q, hG, hQ, hzero, hLip, hdecode, hext⟩ :=
    exists_ambient_local_coefficient_data (L := L) F he hU hρ hK hsub w hTcap hTcapb
      hjet hunit
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : SecondCountableTopology (lp (fun _ : ℤ => ℂ) 2) :=
    secondCountable_of_countable_hilbertBasis
      (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (lp (fun _ : ℤ => ℂ) 2)))
  obtain ⟨Bmul, hcomplex, _hBnorm, hreal⟩ := exists_vectorPeriodicH1_product (L := L) (ι := ι)
  obtain ⟨T, hT, hTTcap, hT1, F0, u, U0, V, _hFcap, hU0, hwU0, hV, hwV,
      huw, hu, hpath, hinside, heq, hunique, _htraceBound⟩ :=
    exists_open_smooth_coefficient_parameter_response lambda w hTcap (rcap := 1) zero_lt_one
      Bmul G Q hG hQ hzero hLip hO hw hext
  let B : Set S := U0 ∩ (fun z : S => (z, u z)) ⁻¹' V
  have hB : IsOpen B :=
    (continuousOn_id.prodMk hu.continuousOn).isOpen_inter_preimage hU0 hV
  have hwB : w ∈ B := ⟨hwU0, by simpa only [mem_preimage, huw] using hwV⟩
  have hM := vectorPeriodicH1_product_spectralTranslation Bmul hcomplex
  let coord : ((Fin 2 × ι) → ℝ) → W × W := fun j =>
    (WithLp.toLp 2 (fun i => j (0, i)), WithLp.toLp 2 (fun i => j (1, i)))
  let g := fun t j => 1 - ambientCurvePrincipal F ρ (a + t) (coord j).1 (coord j).2
  let q := fun t j i => ambientCurveLower F e ρ (a + t) (coord j).1 (coord j).2 i
  have hdecode' (t : ℝ) (z : S) (ht : 0 ≤ t) (hz : (t, z) ∈ O) (x : AddCircle L) :
      periodicSobolevJet (L := L) 0 0 (by omega) (G (t, z)) x =
        (g t (fun j => vectorPeriodicJet (L := L) 1 j.1 (by omega) z x j.2) : ℂ) ∧
      ∀ i, periodicSobolevJet (L := L) 0 0 (by omega)
          (complexLpRealEquiv.symm (lpFinitePiEquiv ℝ (Q (t, z)) i)) x =
        (q t (fun j => vectorPeriodicJet (L := L) 1 j.1 (by omega) z x j.2) i : ℂ) :=
    hdecode t z ht hz x
  have hcoeff := fun s t z ht hz hsz =>
    local_periodicH1_coefficients_spectralTranslation G Q g q hdecode' s
      (t := t) (u := z) ht hz hsz
  refine ⟨T, hT, hTTcap, hT1, F0, u, B, hB, hwB, huw,
    hu.mono inter_subset_left, hpath.mono inter_subset_left, ?_, ?_, ?_⟩
  · intro z hz
    apply eventually_initialBranch_spectralTranslation Bmul G Q hM hO hcoeff
      hT.le z (u z) u (heq z hz.1) _ (hinside z hz.1)
    filter_upwards [hV.mem_nhds hz.2] with y hy
    exact hunique y hy
  · intro z hz t x
    exact (hOU _ (hinside z hz.1 t)).2 x
  · intro z hz
    filter_upwards [heq z hz.1, (initialResponseTrace_spec lambda z hT.le (u z)).2.2.2]
      with t hsource hhigh
    intro ht x i
    let Z := initialResponseTrace lambda z hT.le (u z) ⟨t, ht⟩
    let H := initialHeatHigh lambda z t + shiftedHighOperator hT.le lambda (u z) t
    have hlocal := vectorPeriodic_correctedSource_at_trace (L := L)
      H Z (Q (t, Z)) (G (t, Z))
      (fun x => ambientCurvePrincipal F ρ (a + t) (jet Z x).1 (jet Z x).2)
      (fun x => ambientCurveLower F e ρ (a + t) (jet Z x).1 (jet Z x).2)
      Bmul (hhigh ht)
      (fun x => (hdecode t Z ht.1 (hinside z hz.1 ⟨t, ht⟩) x).1)
      (fun x i => (hdecode t Z ht.1 (hinside z hz.1 ⟨t, ht⟩) x).2 i) hreal x i
    rw [hsource ht]
    exact hlocal

end PoincareConjecture.M63

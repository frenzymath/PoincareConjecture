import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralResponseCurve
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.SpectralTraceDecoding
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCurveCoefficients
import PoincareConjecture.Proofs.M63.Mathlib.ClassicalPrimitive
import PoincareConjecture.Proofs.M63.Mathlib.ContinuousPartialDerivatives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M63

open SpectralHeatNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b L T : ℝ} [Fact (0 < L)]

local notation "W" => EuclideanSpace ℝ ι
local notation "S" => State ((ℤ × Fin 2) × ι)

theorem initialResponseCurve_classical (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U)
    (hT : 0 ≤ T) (hTb : a + T ≤ b) (w : S)
    (F0 : ForcingSpace ((ℤ × Fin 2) × ι) T) :
    let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
    let V := initialResponseTrace lambda w hT F0
    let q := initialResponseCurve (L := L) hT w F0
    ContDiffAt ℝ ∞ (fun s : ℝ => initialResponseTrace lambda
      (vectorPeriodicSpectralTranslation (L := L) s w) hT
      ((vectorPeriodicSpectralTranslation (L := L) s).compLpL 2 (timeMeasure T) F0)) 0 →
    (∀ t : Icc (0 : ℝ) T, ∀ x : AddCircle L,
      let z := WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 0 (by omega) (V t) x)
      let v := WithLp.toLp 2 (vectorPeriodicJet (L := L) 1 1 (by omega) (V t) x)
      z ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z v ≠ 0) →
    (∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T, ∀ x i,
      let z := WithLp.toLp 2
        (vectorPeriodicJet (L := L) 1 0 (by omega) (V ⟨t, ht⟩) x)
      let v := WithLp.toLp 2
        (vectorPeriodicJet (L := L) 1 1 (by omega) (V ⟨t, ht⟩) x)
      vectorPeriodicJet (L := L) 0 0 (by omega) (F0 t) x i =
        (ambientCurvePrincipal F ρ (a + t) z v - 1) *
          vectorPeriodicJet (L := L) 2 2 (by omega)
            (initialHeatHigh lambda w t + shiftedHighOperator hT lambda F0 t) x i +
          ambientCurveLower F e ρ (a + t) z v i) →
    (∀ t ∈ Ioo (0 : ℝ) T, ∀ x : ℝ, HasDerivAt (fun s => q s x)
      (ambientCurvePrincipal F ρ (a + t) (q t x) (deriv (q t) x) •
          iteratedDeriv 2 (q t) x +
        ambientCurveLower F e ρ (a + t) (q t x) (deriv (q t) x)) t) ∧
      ContDiffOn ℝ 1 (Function.uncurry q) (Ioo (0 : ℝ) T ×ˢ univ) := by
  classical
  dsimp only
  intro horbit hinside hsource
  let lambda := fun p : (ℤ × Fin 2) × ι => periodicSpectrum L p.1
  let V := initialResponseTrace lambda w hT F0
  let E : (ι → ℝ) ≃L[ℝ] W :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm
  let q := initialResponseCurve (L := L) hT w F0
  let qx : ℝ → ℝ → W := fun t x => E
    (vectorPeriodicJet (L := L) 1 1 (by omega)
      (V (projIcc 0 T hT t)) (x : AddCircle L))
  obtain ⟨hqc, _hperiod, hqzero, hqderiv⟩ :=
    initialResponseCurve_spec (L := L) hT w F0
  obtain ⟨_hspace, hjets⟩ :=
    initialResponseCurve_spatial_jets (L := L) hT w F0 horbit
  obtain ⟨J2, hJ2⟩ := hjets 2
  let qxx : ℝ → ℝ → W := fun t x => J2 (projIcc 0 T hT t) (x : AddCircle L)
  have hqx (t x : ℝ) : deriv (q t) x = qx t x := (hqderiv t x).deriv
  have hqxx (t : Icc (0 : ℝ) T) (x : ℝ) :
      iteratedDeriv 2 (q (t : ℝ)) x = qxx (t : ℝ) x := by
    simpa only [qxx, projIcc_val] using hJ2 t x
  have hqxc : Continuous (Function.uncurry qx) := by
    exact E.continuous.comp (continuous_eval.comp
      (((vectorPeriodicJet (L := L) (ι := ι) 1 1 (by omega)).continuous.comp
        (V.continuous.comp (continuous_projIcc.comp continuous_fst))).prodMk
          ((AddCircle.continuous_mk' L).comp continuous_snd)))
  have hqxxc : Continuous (Function.uncurry qxx) :=
    continuous_eval.comp ((J2.continuous.comp
      (continuous_projIcc.comp continuous_fst)).prodMk
        ((AddCircle.continuous_mk' L).comp continuous_snd))
  have hinside' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (x : ℝ) :
      q t x ∈ U ∧ mfderiv 𝓘(ℝ, W) (𝓡 n) ρ (q t x) (qx t x) ≠ 0 := by
    change E (vectorPeriodicJet (L := L) 1 0 (by omega)
      (V (projIcc 0 T hT t)) (x : AddCircle L)) ∈ U ∧
      mfderiv 𝓘(ℝ, W) (𝓡 n) ρ
        (E (vectorPeriodicJet (L := L) 1 0 (by omega)
          (V (projIcc 0 T hT t)) (x : AddCircle L)))
        (E (vectorPeriodicJet (L := L) 1 1 (by omega)
          (V (projIcc 0 T hT t)) (x : AddCircle L))) ≠ 0
    rw [projIcc_of_mem hT ht]
    exact hinside ⟨t, ht⟩ (x : AddCircle L)
  let param : ℝ × ℝ → (ℝ × W) × W := fun z => ((a + z.1, q z.1 z.2), qx z.1 z.2)
  have hparam : Continuous param :=
    ((continuous_const.add continuous_fst).prodMk hqc).prodMk hqxc
  have hmap : MapsTo param (Icc (0 : ℝ) T ×ˢ univ)
      {z : (ℝ × W) × W | z.1.1 ∈ Icc a b ∧ z.1.2 ∈ U ∧
        mfderiv 𝓘(ℝ, W) (𝓡 n) ρ z.1.2 z.2 ≠ 0} := by
    intro z hz
    refine ⟨⟨?_, ?_⟩, hinside' z.1 hz.1 z.2⟩
    · change a ≤ a + z.1
      linarith [hz.1.1]
    · change a + z.1 ≤ b
      linarith [hz.1.2]
  let R : ℝ → ℝ → W := fun t x =>
    ambientCurvePrincipal F ρ (a + t) (q t x) (qx t x) • qxx t x +
      ambientCurveLower F e ρ (a + t) (q t x) (qx t x)
  obtain ⟨hA, hB, _hpos⟩ := ambientCurveCoefficients_contDiffOn F he hU hρ
  have hAc : ContinuousOn (fun z : ℝ × ℝ =>
      ambientCurvePrincipal F ρ (a + z.1) (q z.1 z.2) (qx z.1 z.2))
      (Icc (0 : ℝ) T ×ˢ univ) := by
    change ContinuousOn ((fun z : (ℝ × W) × W =>
      ambientCurvePrincipal F ρ z.1.1 z.1.2 z.2) ∘ param) _
    exact hA.continuousOn.comp hparam.continuousOn hmap
  have hBc : ContinuousOn (fun z : ℝ × ℝ =>
      ambientCurveLower F e ρ (a + z.1) (q z.1 z.2) (qx z.1 z.2))
      (Icc (0 : ℝ) T ×ˢ univ) := by
    change ContinuousOn ((fun z : (ℝ × W) × W =>
      ambientCurveLower F e ρ z.1.1 z.1.2 z.2) ∘ param) _
    exact hB.continuousOn.comp hparam.continuousOn hmap
  have hRc : ContinuousOn (Function.uncurry R) (Icc (0 : ℝ) T ×ˢ univ) :=
    (hAc.smul hqxxc.continuousOn).add hBc
  let D := fun t => -initialHeatGenerator lambda w t + derivativeState lambda F0 t
  have hD := (initialResponseTrace_integral lambda w hT F0).1
  have htime (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (x : ℝ) :
      HasDerivAt (fun s => q s x) (R t x) t := by
    let Dx : S →L[ℝ] W := E.toContinuousLinearMap.comp
      ((ContinuousMap.evalCLM ℝ (x : AddCircle L)).comp
        (vectorPeriodicJet (L := L) (ι := ι) 0 0 (by omega)))
    have hint : IntervalIntegrable (fun s => Dx (D s)) volume 0 T :=
      ⟨Dx.integrable_comp hD.1, Dx.integrable_comp hD.2⟩
    have hRx : ContinuousOn (fun s => R s x) (Icc (0 : ℝ) T) := by
      change ContinuousOn ((Function.uncurry R) ∘ (fun s : ℝ => (s, x))) _
      exact hRc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, mem_univ _⟩)
    have heq : (fun s => Dx (D s)) =ᵐ[timeMeasure T] (fun s => R s x) := by
      filter_upwards [initialResponseTrace_decoded_derivative (L := L) w hT F0,
        (initialResponseTrace_spec lambda w hT F0).2.2.2, hsource,
        ae_restrict_mem measurableSet_Ioc] with s hdecode hhigh hforcing hs
      have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
      let H := initialHeatHigh lambda w s + shiftedHighOperator hT lambda F0 s
      have hqclosed : q s = E.toContinuousLinearMap ∘ (fun y : ℝ =>
          vectorPeriodicJet (L := L) 1 0 (by omega) (V ⟨s, hs'⟩) (y : AddCircle L)) := by
        funext y
        simp only [q, initialResponseCurve, projIcc_of_mem hT hs']
        rfl
      have hdecodedSmooth : ContDiff ℝ ∞ (fun y : ℝ =>
          vectorPeriodicJet (L := L) 1 0 (by omega) (V ⟨s, hs'⟩) (y : AddCircle L)) :=
        (initialResponseTrace_spatial_jets (L := L) hT w F0 horbit).1 ⟨s, hs'⟩
      have hsecond : qxx s x = E
          (vectorPeriodicJet (L := L) 2 2 (by omega) H (x : AddCircle L)) := by
        rw [← hqxx ⟨s, hs'⟩ x, hqclosed,
          iteratedDeriv_comp_clm E.toContinuousLinearMap 2
            (hdecodedSmooth.contDiffAt.of_le
              (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),
          (vectorPeriodicJet_high_second_derivative (L := L) H (V ⟨s, hs'⟩)
            (hhigh hs') x).2]
        rfl
      change E (vectorPeriodicJet (L := L) 0 0 (by omega) (D s) (x : AddCircle L)) = _
      rw [show vectorPeriodicJet (L := L) 0 0 (by omega) (D s) =
          vectorPeriodicJet (L := L) 2 2 (by omega) H +
            vectorPeriodicJet (L := L) 0 0 (by omega) (F0 s) from hdecode hs']
      change E (vectorPeriodicJet (L := L) 2 2 (by omega) H (x : AddCircle L) +
        vectorPeriodicJet (L := L) 0 0 (by omega) (F0 s) (x : AddCircle L)) = _
      dsimp only [R]
      rw [hsecond]
      apply PiLp.ext
      intro i
      have hfi : vectorPeriodicJet (L := L) 0 0 (by omega) (F0 s) (x : AddCircle L) i =
        (ambientCurvePrincipal F ρ (a + s) (q s x) (qx s x) - 1) *
          vectorPeriodicJet (L := L) 2 2 (by omega) H (x : AddCircle L) i +
          ambientCurveLower F e ρ (a + s) (q s x) (qx s x) i := by
        dsimp only [q, qx, initialResponseCurve]
        rw [projIcc_of_mem hT hs']
        exact hforcing hs' (x : AddCircle L) i
      change vectorPeriodicJet (L := L) 2 2 (by omega) H (x : AddCircle L) i +
          vectorPeriodicJet (L := L) 0 0 (by omega) (F0 s) (x : AddCircle L) i =
        ambientCurvePrincipal F ρ (a + s) (q s x) (qx s x) *
          vectorPeriodicJet (L := L) 2 2 (by omega) H (x : AddCircle L) i +
          ambientCurveLower F e ρ (a + s) (q s x) (qx s x) i
      rw [hfi]
      ring
    have hprimitive (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
        q s x = q 0 x + ∫ r in (0 : ℝ)..s, Dx (D r) := by
      have hp := initialResponseTrace_integral_comp lambda w hT F0 Dx ⟨s, hs⟩
      have hDx (v : S) : Dx (shiftedBaseMultiplier lambda v) =
          E (vectorPeriodicJet (L := L) 1 0 (by omega) v (x : AddCircle L)) := by
        change E (vectorPeriodicJet (L := L) 0 0 (by omega)
          (shiftedBaseMultiplier lambda v) (x : AddCircle L)) = _
        rw [vectorPeriodicJet_shiftedBase]
      rw [hDx, hDx] at hp
      have hq0 : q 0 x = E (vectorPeriodicJet (L := L) 1 0 (by omega) w
          (x : AddCircle L)) := hqzero x
      rw [hq0]
      dsimp only [q, initialResponseCurve]
      rw [projIcc_of_mem hT hs]
      exact hp
    exact hasDerivAt_of_ae_continuous_primitive hT hint hRx heq hprimitive ht
  constructor
  · intro t ht x
    simpa only [R, ← hqx, ← hqxx ⟨t, Ioo_subset_Icc_self ht⟩ x] using htime t ht x
  · let R' : ℝ → ℝ → ℝ →L[ℝ] W := fun t x =>
      ContinuousLinearMap.toSpanSingleton ℝ (R t x)
    let X' : ℝ → ℝ → ℝ →L[ℝ] W := fun t x =>
      ContinuousLinearMap.toSpanSingleton ℝ (qx t x)
    have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set ℝ) ⊆ Icc (0 : ℝ) T ×ˢ univ :=
      prod_mono Ioo_subset_Icc_self Subset.rfl
    apply contDiffOn_one_uncurry_of_partials (isOpen_Ioo.prod isOpen_univ)
      (f₁ := R') (f₂ := X')
    · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ W).continuous.comp_continuousOn
        (hRc.mono hsub)
    · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ W).continuous.comp hqxc).continuousOn
    · intro p hp
      exact (htime p.1 hp.1 p.2).hasFDerivAt
    · intro p _hp
      exact (hqderiv p.1 p.2).hasFDerivAt

end PoincareConjecture.M63

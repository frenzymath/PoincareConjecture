import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.SmoothFormEntropy
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.TimePotentialContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory Filter
open scoped SchwartzMap ContDiff Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem fieldIntegral_schwartz (F : V × V → ℝ) (X : 𝓢(V, V)) :
    fieldIntegral F (X.toLp 2 volume) = ∫ x, F (x, X x) := by
  apply integral_congr_ae
  filter_upwards [X.coeFn_toLp 2 volume] with x hx
  rw [hx]

def rawEntropyFormRate {K : Set V} (hK : IsClosed K) {g : RiemannianMetric n V}
    (D : LeviCivitaData g) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (Q : ℝ)
    (u z : PiLp 2 (fun _ : Fin n => dirichletForm K)) : ℝ :=
  inner ℝ (finiteHilbertMap (dirichletInclusion K) z) (rawLowerFormOperator D hK η hη u) -
    principalVectorEnergy K (rawCutoffPrincipalCoefficient g η hη) z u +
      fieldIntegral (metricEntropyTimePotential D η Q) (dirichletFieldValue K u)

theorem rawEntropyFormRate_continuous {K : Set V} (hK : IsClosed K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) {Q : ℝ} (hQ : 0 ≤ Q) :
    Continuous (fun p : (PiLp 2 (fun _ : Fin n => dirichletForm K)) ×
        (PiLp 2 (fun _ : Fin n => dirichletForm K)) => rawEntropyFormRate hK D η hη Q p.1 p.2) := by
  let I := finiteHilbertMap (m := n) (dirichletInclusion K)
  let L := rawLowerFormOperator D hK η hη
  let A := rawCutoffPrincipalCoefficient g η hη
  have hE : Continuous (fun p : (PiLp 2 (fun _ : Fin n => dirichletForm K)) ×
      (PiLp 2 (fun _ : Fin n => dirichletForm K)) => principalVectorEnergy K A p.2 p.1) := by
    have hc := continuous_snd.inner (𝕜 := ℝ)
      ((finiteHilbertMap (m := n) (principalFormOperator K A)).continuous.comp continuous_fst)
    simpa only [principalVectorEnergy_pairing, Function.comp_def] using hc
  exact (((I.continuous.comp continuous_snd).inner (𝕜 := ℝ)
    (L.continuous.comp continuous_fst)).sub hE).add
      ((metricEntropyTimePotential_field_continuous D η.smooth' hη hQ).comp
        ((dirichletFieldValue K).continuous.comp continuous_fst))

theorem rawEntropyFormRate_test_nonpos {K : Set V} (hK : IsCompact K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (hR : ∀ x, 0 ≤ D.scalarCurvature x)
    (f : Fin n → supportedTests K) :
    rawEntropyFormRate hK.isClosed D η hη Q (vectorTestForm K f)
      (vectorTestForm K (metricEntropySupportedTests hK g η η.smooth' Q f)) ≤ 0 := by
  unfold rawEntropyFormRate
  have hvalue := congrArg (fieldIntegral (metricEntropyTimePotential D η Q))
    (dirichletFieldValue_test K f)
  have he := hvalue.trans (fieldIntegral_schwartz (metricEntropyTimePotential D η Q)
    (schwartzField (fun j => (f j : 𝓢(V, ℝ)))))
  rw [he]
  exact raw_smooth_form_entropy_nonpos hK D η hη hηK hQ hR f

theorem exists_metric_entropy_dissipating_test {K : Set V} (hK : IsCompact K)
    {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hηK : ∀ x ∈ K, η x = 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (hR : ∀ x, 0 ≤ D.scalarCurvature x)
    (u : PiLp 2 (fun _ : Fin n => dirichletForm K)) :
    ∃ z : PiLp 2 (fun _ : Fin n => dirichletForm K),
      (∀ j : Fin n, (dirichletInclusion K (z j) : L2) =ᵐ[volume]
        fun x => metricEntropyTest g η Q (EuclideanSpace.single j 1)
          (x, dirichletFieldValue K u x)) ∧ rawEntropyFormRate hK.isClosed D η hη Q u z ≤ 0 := by
  obtain ⟨f, z, hflim, hzlim, hz⟩ :=
    exists_metric_entropy_form_test hK g η η.smooth' hη Q u
  refine ⟨z, hz, ?_⟩
  have hlim := ((rawEntropyFormRate_continuous hK.isClosed D η hη hQ).tendsto (u, z)).comp
    (hflim.prodMk_nhds hzlim)
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun k => rawEntropyFormRate_test_nonpos hK D η hη hηK hQ hR (f k)

end PoincareConjecture.M35.Uniqueness.Heat

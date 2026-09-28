import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberRestriction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.Variation.Proper
open Set MeasureTheory PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.RiemannianMetric.openFiber_closedBand_integrals_of_proper_restriction
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M] [IsManifold (𝓡 (m+k)) ∞ M]
    (g : RiemannianMetric (m+k) M) {f : M → Fin k → ℝ}
    (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
    (U V : TopologicalSpace.Opens M) (hVU : (V:Set M)⊆U)
    (hreg : ∀ x∈U, Function.Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x))
    (c : Fin k → ℝ) (F : M → ℝ) {I : Set ℝ}
    (hproper : IsProperMap (I.restrictPreimage (F ∘ openFiberIncl f V c))) :
    let hregV := fun x hx => hreg x (hVU hx)
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k)))=m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    letI := openFiberChartedSpace (m := m) hf V hregV c
    letI := isManifold_openFiber (m := m) hf V hregV c
    let gU := g.openRegularFiberMetric hf U hreg c
    let gV := g.openRegularFiberMetric hf V hregV c
    let j : openFiber f V c → openFiber f U c := fun x =>
      ⟨⟨openFiberIncl f V c x,hVU x.1.2⟩,x.2⟩
    ∀ a b : ℝ, Icc a b⊆I →
      (∀ Ψ : ℝ → ℝ,
        (∫ x in (F ∘ openFiberIncl f V c) ⁻¹' Icc a b,
          Ψ (gV.leviCivitaData.scalarCurvature x) ∂gV.volumeMeasure) =
        ∫ x in {x : openFiber f U c | openFiberIncl f U c x∈V ∧
          F (openFiberIncl f U c x)∈Icc a b},
          Ψ (gU.leviCivitaData.scalarCurvature x) ∂gU.volumeMeasure) ∧
      ∀ K : openFiber f U c → ℝ,
        (∫ x in (F ∘ openFiberIncl f V c) ⁻¹' Icc a b,
          K (j x) ∂gV.volumeMeasure) =
        ∫ x in {x : openFiber f U c | openFiberIncl f U c x∈V ∧
          F (openFiberIncl f U c x)∈Icc a b}, K x ∂gU.volumeMeasure := by
  dsimp only
  let hregV := fun x hx => hreg x (hVU hx)
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k)))=m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let := openFiberChartedSpace (m := m) hf V hregV c
  let := isManifold_openFiber (m := m) hf V hregV c
  let gU := g.openRegularFiberMetric hf U hreg c
  let gV := g.openRegularFiberMetric hf V hregV c
  let j : openFiber f V c → openFiber f U c := fun x =>
    ⟨⟨openFiberIncl f V c x,hVU x.1.2⟩,x.2⟩
  intro a b hab
  let A := (F ∘ openFiberIncl f V c) ⁻¹' Icc a b
  have hA : IsCompact A := Poincare.Coarea.isCompact_slab_of_isProperMap hproper hab
  have himage : j '' A = {x : openFiber f U c | openFiberIncl f U c x∈V ∧
      F (openFiberIncl f U c x)∈Icc a b} := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.1.2,hz⟩
    · intro hx
      refine ⟨⟨⟨openFiberIncl f U c x,hx.1⟩,x.2⟩,hx.2,?_⟩
      rfl
  obtain ⟨_,_,_,_,htrans⟩ := g.openRegularFiberMetric_restriction_transport hf U V hVU hreg c
  obtain ⟨_,hweight,hscalar⟩ := htrans A hA
  change j '' A = _ at himage
  constructor
  · intro Ψ
    have hs := hscalar Ψ
    change (∫ x in A, Ψ (gV.leviCivitaData.scalarCurvature x) ∂gV.volumeMeasure) =
      ∫ x in j '' A, Ψ (gU.leviCivitaData.scalarCurvature x) ∂gU.volumeMeasure at hs
    rw [himage] at hs
    exact hs
  · intro K
    have hw := hweight K
    change (∫ x in A, K (j x) ∂gV.volumeMeasure) =
      ∫ x in j '' A, K x ∂gU.volumeMeasure at hw
    rw [himage] at hw
    exact hw

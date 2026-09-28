import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.ComponentRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace MeasureTheory
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology

theorem PoincareConjecture.RiemannianMetric.exists_openFiber_component_equivalence_of_region
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + k))) M]
    [IsManifold (𝓡 (m + k)) ∞ M]
    (g : PoincareConjecture.RiemannianMetric (m + k) M)
    {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) ∞ f)
    (U : Opens M) (hreg : ∀ x ∈ U, Function.Surjective
      (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x)) (c : Fin k → ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let L := openFiber f U c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    ∀ (p : L) (V : Opens M), (V : Set M) ⊆ U →
      incl ⁻¹' (V : Set M) = connectedComponent p →
      ∀ hregV : ∀ x ∈ V, Function.Surjective
        (mfderiv (𝓡 (m + k)) 𝓘(ℝ, Fin k → ℝ) f x),
        letI := openFiberChartedSpace (m := m) hf V hregV c
        letI := isManifold_openFiber (m := m) hf V hregV c
        let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) p
        let gC := gL.connectedComponentMetric p
        let gV := g.openRegularFiberMetric hf V hregV c
        ∃ e : C ≃ₘ⟮𝓡 m, 𝓡 m⟯ openFiber f V c,
          (∀ x : C, openFiberIncl f V c (e x) = incl x.val) ∧
          ConnectedSpace (openFiber f V c) ∧
          (IsCompact (connectedComponent p) → CompactSpace (openFiber f V c)) ∧
          (∀ (x : C) (v w : TangentSpace (𝓡 m) x),
            gV.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x v)
              (mfderiv (𝓡 m) (𝓡 m) e x w) = gC.inner x v w) ∧
          (∀ x y : C, gV.edist (e x) (e y) = gC.edist x y) ∧
          MeasurePreserving e gC.volumeMeasure gV.volumeMeasure ∧
          (∀ x : C, gC.leviCivitaData.scalarCurvature x =
            gV.leviCivitaData.scalarCurvature (e x)) ∧
          ∀ F : openFiber f V c → ℝ,
            (∫ x, F (e x) ∂gC.volumeMeasure) = ∫ y, F y ∂gV.volumeMeasure := by
  classical
  dsimp only
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + k))) = m + k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  let L := openFiber f U c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  intro p V hVU hVC hregV
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin m)) p
  obtain ⟨V₀, hV₀U, hV₀C, hreg₀, e₀, he₀, _, _, hm₀, hd₀, _⟩ :=
    g.exists_openFiber_connectedComponent_restriction hf U hreg c p
  let := openFiberChartedSpace (m := m) hf V₀ hreg₀ c
  let := isManifold_openFiber (m := m) hf V₀ hreg₀ c
  let := openFiberChartedSpace (m := m) hf V hregV c
  let := isManifold_openFiber (m := m) hf V hregV c
  have hsame : ∀ x, (x ∈ V₀ ∧ f x = c) ↔ (x ∈ V ∧ f x = c) := by
    intro x
    constructor
    · rintro ⟨hx, hfx⟩
      let y : L := ⟨⟨x, hV₀U hx⟩, hfx⟩
      have hy : y ∈ connectedComponent p := by rw [← hV₀C]; exact hx
      refine ⟨?_, hfx⟩
      have : y ∈ incl ⁻¹' (V : Set M) := by rw [hVC]; exact hy
      exact this
    · rintro ⟨hx, hfx⟩
      let y : L := ⟨⟨x, hVU hx⟩, hfx⟩
      have hy : y ∈ connectedComponent p := by rw [← hVC]; exact hx
      refine ⟨?_, hfx⟩
      have : y ∈ incl ⁻¹' (V₀ : Set M) := by rw [hV₀C]; exact hy
      exact this
  let e₁ := openFiberDiffeomorphOfEq (m := m) hf hf hreg₀ hregV hsame
  let e := e₀.trans e₁
  let gC := gL.connectedComponentMetric p
  let gV := g.openRegularFiberMetric hf V hregV c
  have hincl (x : C) : openFiberIncl f V c (e x) = incl x.val := he₀ x
  have hmetric (x : C) (v w : TangentSpace (𝓡 m) x) :
      gV.inner (e x) (mfderiv (𝓡 m) (𝓡 m) e x v)
        (mfderiv (𝓡 m) (𝓡 m) e x w) = gC.inner x v w := by
    have hcomp := mfderiv_comp x
      (e₁.contMDiff.mdifferentiable (by simp) (e₀ x))
      (e₀.contMDiff.mdifferentiable (by simp) x)
    change mfderiv (𝓡 m) (𝓡 m) e x = _ at hcomp
    rw [hcomp]
    change gV.inner (e₁ (e₀ x))
      (mfderiv (𝓡 m) (𝓡 m) e₁ (e₀ x) (mfderiv (𝓡 m) (𝓡 m) e₀ x v))
      (mfderiv (𝓡 m) (𝓡 m) e₁ (e₀ x) (mfderiv (𝓡 m) (𝓡 m) e₀ x w)) = _
    have hm₁ := g.openRegularFiberMetric_inner_equivOfEq hf hf hreg₀ hregV hsame
      (e₀ x) (mfderiv (𝓡 m) (𝓡 m) e₀ x v) (mfderiv (𝓡 m) (𝓡 m) e₀ x w)
    exact hm₁.symm.trans (hm₀ x v w)
  have hedist := gC.edist_eq_of_diffeomorph_metric_pullback gV e
    (fun x v w => (hmetric x v w).symm)
  refine ⟨e, hincl, e.surjective.connectedSpace e.continuous, ?_,
    hmetric, hedist, ?_, ?_, ?_⟩
  · intro hcompact
    let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
    exact e.toHomeomorph.compactSpace
  · exact gC.measurePreserving_volumeMeasure_of_edist_eq gV e.toEquiv hedist
  · intro x
    exact gC.leviCivitaData.scalarCurvature_eq_of_local_isometry gV.leviCivitaData
      isOpen_univ e.contMDiff.contMDiffOn (fun x _ v w => (hmetric x v w).symm) (mem_univ x)
  · intro F
    exact gC.integral_comp_equiv_volumeMeasure gV e.toEquiv hedist F

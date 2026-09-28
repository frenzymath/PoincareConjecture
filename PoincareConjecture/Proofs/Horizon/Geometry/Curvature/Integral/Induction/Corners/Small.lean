import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Induction.Corners.Normalized
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Small
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Hessian.Pullback







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

open Set Function TopologicalSpace MeasureTheory PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Topology Bundle

universe u



theorem PoincareConjecture.normalizedCornerScalarBound_of_small
    {n m k : ℕ} (hdim : n = m + k) (δ H η C : ℝ)
    (hsmall : ∀ (M : Type) [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
      [MeasurableSpace M] [BorelSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M],
      PoincareConjecture.NormalizedCornerScalarBound n m k hdim M δ H η C) :
    ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
      [MeasurableSpace M] [BorelSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M],
      PoincareConjecture.NormalizedCornerScalarBound n m k hdim M δ H η C := by
  classical
  intro M _ _ _ _ _ _ _ g D hc hsec f h hf hh U hunit hpair hcross htight hhess
  let F := fun x i => f i x
  have hF : ContMDiff (𝓡 n) 𝓘(ℝ,Fin k → ℝ) ∞ F := contMDiff_pi_space.mpr hf
  change ∀ (hreg : ∀ x ∈ U, Surjective (mfderiv (𝓡 n) 𝓘(ℝ,Fin k → ℝ) F x))
    (c : Fin k → ℝ), _
  intro hreg c
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))=m+k) :=
    ⟨by rw [finrank_euclideanSpace_fin]; exact hdim⟩
  let := openFiberChartedSpace (m := m) hF U hreg c
  let := isManifold_openFiber (m := m) hF U hreg c
  let L := openFiber F U c
  let incl := openFiberIncl F U c
  let gL : RiemannianMetric m L := RiemannianMetric.Induced.pullbackMetric g incl
    (contMDiff_openFiberIncl (m := m) hF U hreg c)
    (injective_mfderiv_openFiberIncl (m := m) hF U hreg c)
  change CompactSpace L → ConnectedSpace L → MetricComplete gL →
    (∀ x y : L, gL.edist x y ≤ 1) →
    (∀ x : L, ∀ y : M, g.edist (incl x) y ≤ ENNReal.ofReal η → y ∈ U) →
    ∀ K : L → ℝ, Continuous K → (∀ x, 0 ≤ K x) →
    (∀ x (v w : TangentSpace (𝓡 m) x),
      -K x ≤ gL.leviCivitaData.sectionalCurvature x v w) → _
  intro hcompact hconnected hcL hdiam hbuffer K hK hKpos hKsec
  let : CompactSpace L := hcompact
  let : ConnectedSpace L := hconnected
  let : SecondCountableTopology M := g.secondCountableTopology
  let : Small.{0} M := Poincare.Topology.SecondCountable.small M
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Shrink.{0} M) :=
    Poincare.Manifold.shrinkChartedSpace _ M
  let : IsManifold (𝓡 n) ∞ (Shrink.{0} M) :=
    Poincare.Manifold.shrinkIsManifold (𝓡 n) M
  let : T3Space (Shrink.{0} M) :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).t3Space
  let : MeasurableSpace (Shrink.{0} M) := borel (Shrink.{0} M)
  let : BorelSpace (Shrink.{0} M) := ⟨rfl⟩
  let : PreconnectedSpace (Shrink.{0} M) := RiemannianMetric.shrink_preconnectedSpace
  let e := (Poincare.Manifold.shrinkDiffeomorph (𝓡 n) M).symm
  let g₀ := g.shrink
  let D₀ := g₀.leviCivitaData
  have he (x : Shrink.{0} M) (v w : TangentSpace (𝓡 n) x) :
      g₀.inner x v w = g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) := rfl
  have hinv (x : Shrink.{0} M) : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible :=
    ⟨e.isLocalDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x,rfl⟩
  have hgrad (u : M → ℝ) (hu : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ u) (x : Shrink.{0} M) :
      mfderiv (𝓡 n) (𝓡 n) e x (D₀.gradient (u ∘ e) x) = D.gradient u (e x) := by
    rw [D₀.gradient_comp_eq_mpullback D
      (e.contMDiff.mdifferentiable (by simp) x)
      (hu.mdifferentiable (by simp) (e x)) (hinv x) (he x)]
    exact (hinv x).self_apply_inverse _
  have hnorm (u : M → ℝ) (hu : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ u) (x : Shrink.{0} M) :
      g₀.tangentNorm x (D₀.gradient (u ∘ e) x) =
        g.tangentNorm (e x) (D.gradient u (e x)) := by
    simp only [RiemannianMetric.tangentNorm, he, hgrad u hu]
  have hess (u : M → ℝ) (hu : ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ u) (x : Shrink.{0} M)
      (v w : TangentSpace (𝓡 n) x) :
      D₀.hessian (u ∘ e) x v w = D.hessian u (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w) :=
    D₀.hessian_comp_of_metric_pullback D (e.contMDiff x)
      (Filter.Eventually.of_forall hinv) (Filter.Eventually.of_forall he) (hu (e x)) v w
  let f₀ : Fin k → Shrink.{0} M → ℝ := fun i => f i ∘ e
  let h₀ : Fin k → Shrink.{0} M → ℝ := fun i => h i ∘ e
  have hf₀ : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (f₀ i) := fun i => (hf i).comp e.contMDiff
  have hh₀ : ∀ i, ContMDiff (𝓡 n) 𝓘(ℝ,ℝ) ∞ (h₀ i) := fun i => (hh i).comp e.contMDiff
  let V : Opens (Shrink.{0} M) := ⟨e ⁻¹' U,U.isOpen.preimage e.contMDiff.continuous⟩
  have hunit₀ : ∀ x ∈ V, ∀ i,
      g₀.tangentNorm x (D₀.gradient (f₀ i) x) ≤ 1 ∧
      g₀.tangentNorm x (D₀.gradient (h₀ i) x) ≤ 1 := by
    intro x hx i
    dsimp only [f₀,h₀]
    rw [hnorm (f i) (hf i),hnorm (h i) (hh i)]
    exact hunit (e x) hx i
  have hpair₀ : ∀ x ∈ V, ∀ i,
      g₀.inner x (D₀.gradient (f₀ i) x) (D₀.gradient (h₀ i) x) ≤ -1+2*δ := by
    intro x hx i
    dsimp only [f₀,h₀]
    rw [he,hgrad (f i) (hf i),hgrad (h i) (hh i)]
    exact hpair (e x) hx i
  have hcross₀ : ∀ x ∈ V, ∀ i j, i ≠ j →
      |g₀.inner x (D₀.gradient (f₀ i) x) (D₀.gradient (f₀ j) x)| ≤ δ ∧
      |g₀.inner x (D₀.gradient (f₀ i) x) (D₀.gradient (h₀ j) x)| ≤ δ ∧
      |g₀.inner x (D₀.gradient (h₀ i) x) (D₀.gradient (f₀ j) x)| ≤ δ ∧
      |g₀.inner x (D₀.gradient (h₀ i) x) (D₀.gradient (h₀ j) x)| ≤ δ := by
    intro x hx i j hij
    dsimp only [f₀,h₀]
    simp only [he,hgrad (f i) (hf i),hgrad (f j) (hf j),
      hgrad (h i) (hh i),hgrad (h j) (hh j)]
    exact hcross (e x) hx i j hij
  have htight₀ : ∀ x ∈ V, ∀ i j, i ≠ j →
      g₀.inner x (D₀.gradient (f₀ i) x) (D₀.gradient (f₀ j) x) ≤ 0 := by
    intro x hx i j hij
    dsimp only [f₀]
    rw [he,hgrad (f i) (hf i),hgrad (f j) (hf j)]
    exact htight (e x) hx i j hij
  have hhess₀ : ∀ x ∈ V, ∀ i v,
      D₀.hessian (f₀ i) x v v ≤ H*g₀.inner x v v ∧
      D₀.hessian (h₀ i) x v v ≤ H*g₀.inner x v v := by
    intro x hx i v
    dsimp only [f₀,h₀]
    rw [hess (f i) (hf i),hess (h i) (hh i),he]
    exact hhess (e x) hx i _
  obtain ⟨hreg₀,hE⟩ := g₀.exists_openFiber_diffeomorph_of_diffeomorph
    hdim g e he hF U hreg
  let F₀ : Shrink.{0} M → Fin k → ℝ := F ∘ e
  have hF₀ : ContMDiff (𝓡 n) 𝓘(ℝ,Fin k → ℝ) ∞ F₀ := hF.comp e.contMDiff
  let := openFiberChartedSpace (m := m) hF₀ V hreg₀ c
  let := isManifold_openFiber (m := m) hF₀ V hreg₀ c
  let L₀ := openFiber F₀ V c
  let incl₀ := openFiberIncl F₀ V c
  let gL₀ : RiemannianMetric m L₀ := RiemannianMetric.Induced.pullbackMetric g₀ incl₀
    (contMDiff_openFiberIncl (m := m) hF₀ V hreg₀ c)
    (injective_mfderiv_openFiberIncl (m := m) hF₀ V hreg₀ c)
  obtain ⟨E,hEincl,hEmetric⟩ := hE c
  let : CompactSpace L₀ := E.symm.toHomeomorph.compactSpace
  let : ConnectedSpace L₀ := E.symm.surjective.connectedSpace E.symm.contMDiff.continuous
  have hcL₀ : MetricComplete gL₀ :=
    (RiemannianMetric.metricComplete_iff_diffeomorph gL₀ gL E hEmetric).mpr hcL
  have hdist (x y : L₀) : gL₀.edist x y = gL.edist (E x) (E y) :=
    RiemannianMetric.edist_diffeomorph gL₀ gL E hEmetric x y
  have hdiam₀ : ∀ x y : L₀, gL₀.edist x y ≤ 1 := by
    intro x y
    rw [hdist]
    exact hdiam (E x) (E y)
  have hbuffer₀ : ∀ x : L₀, ∀ y : Shrink.{0} M,
      g₀.edist (incl₀ x) y ≤ ENNReal.ofReal η → y ∈ V := by
    intro x y hy
    rw [RiemannianMetric.edist_diffeomorph g₀ g e he] at hy
    rw [← hEincl x] at hy
    exact hbuffer (E x) (e y) hy
  let K₀ : L₀ → ℝ := K ∘ E
  have hK₀ : Continuous K₀ := hK.comp E.contMDiff.continuous
  have hKpos₀ : ∀ x, 0 ≤ K₀ x := fun x => hKpos (E x)
  have hKsec₀ : ∀ x (v w : TangentSpace (𝓡 m) x),
      -K₀ x ≤ gL₀.leviCivitaData.sectionalCurvature x v w := by
    intro x v w
    rw [RiemannianMetric.sectionalCurvature_diffeomorph gL₀ gL E hEmetric]
    exact hKsec (E x) _ _
  have hb := hsmall (Shrink.{0} M) g₀ D₀
    (g.shrink_metricComplete_iff.mpr hc) (g.shrink_sectionalCurvature_lower_bound D hsec)
    f₀ h₀ hf₀ hh₀ V hunit₀ hpair₀ hcross₀ htight₀ hhess₀ hreg₀ c
    (show CompactSpace L₀ from inferInstance) (show ConnectedSpace L₀ from inferInstance)
    hcL₀ hdiam₀ hbuffer₀ K₀ hK₀ hKpos₀ hKsec₀
  have hs := gL₀.leviCivitaData.integral_scalarCurvature_eq_of_diffeomorph
    gL.leviCivitaData E hEmetric (fun z => max 0 z)
  have hi : (∫ x, K₀ x ∂gL₀.volumeMeasure) = ∫ x, K x ∂gL.volumeMeasure :=
    gL₀.integral_comp_equiv_volumeMeasure gL E.toEquiv
      (fun x y => (hdist x y).symm) K
  change (∫ x, max 0 (gL₀.leviCivitaData.scalarCurvature x) ∂gL₀.volumeMeasure) ≤
    C*(1+∫ x, K₀ x ∂gL₀.volumeMeasure) at hb
  rw [hs,hi] at hb
  exact hb

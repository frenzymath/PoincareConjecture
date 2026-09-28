import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.LocalToGlobal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularFiberOpen
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

open Set MeasureTheory PoincareConjecture
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.RiemannianMetric.integral_openFiber_pos_scalar_le_of_local_bounds
    {m k : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m+k))) M] [IsManifold (𝓡 (m+k)) ∞ M]
    (g : RiemannianMetric (m+k) M) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hn : 1≤m+k)
    (hsec : ∀ x (v w : TangentSpace (𝓡 (m+k)) x), -1≤D.sectionalCurvature x v w)
    {f : M → Fin k → ℝ} (hf : ContMDiff (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) ∞ f)
    (U : TopologicalSpace.Opens M)
    (hreg : ∀ x∈U, Function.Surjective (mfderiv (𝓡 (m+k)) 𝓘(ℝ,Fin k → ℝ) f x))
    (c : Fin k → ℝ) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k)))=m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) hf U hreg c
    letI := isManifold_openFiber (m := m) hf U hreg c
    let L := openFiber f U c
    let incl := openFiberIncl f U c
    let gL := g.openRegularFiberMetric hf U hreg c
    CompactSpace L → Nonempty L → (∀ x y:L, gL.edist x y≤1) →
    ∀ K:L → ℝ, Continuous K → (∀ x, 0≤K x) →
    ∀ r B:ℝ, 0<r → r≤1 → 0≤B →
    (∀ p:L, (∫ x in incl ⁻¹' g.ball (incl p) r,
        max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ≤
      B*(1+∫ x in incl ⁻¹' g.ball (incl p) (2*r), K x ∂gL.volumeMeasure)) →
    (∫ x, max 0 (gL.leviCivitaData.scalarCurvature x) ∂gL.volumeMeasure) ≤
      (⌈RiemannianMetric.modelVolume (m+k) 1 6 /
        RiemannianMetric.modelVolume (m+k) 1 (r/4)⌉₊:ℝ)*B*
          (1+∫ x, K x ∂gL.volumeMeasure) := by
  classical
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k)))=m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) hf U hreg c
  let := isManifold_openFiber (m := m) hf U hreg c
  dsimp only
  let L := openFiber f U c
  let incl := openFiberIncl f U c
  let gL := g.openRegularFiberMetric hf U hreg c
  intro hcompact hnonempty hdiam K hKc hKn r B hr hr1 hB hbound
  let : CompactSpace L := hcompact
  let : Nonempty L := hnonempty
  let p : L := Classical.arbitrary L
  have hincl := contMDiff_openFiberIncl (m := m) hf U hreg c
  have hinside (x:L) : incl x∈g.ball (incl p) 2 := by
    change g.edist (incl p) (incl x)<ENNReal.ofReal 2
    have hd := RiemannianMetric.edist_map_le_of_metric_pullback gL g hincl
      (openRegularFiberMetric_inner hf U hreg c g) p x
    exact (hd.trans (hdiam p x)).trans_lt (by norm_num)
  have hRi : Integrable (fun x:L => max 0 (gL.leviCivitaData.scalarCurvature x))
      gL.volumeMeasure :=
    (continuous_const.max gL.leviCivitaData.continuous_scalarCurvature).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hKi : Integrable K gL.volumeMeasure :=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact g.integral_le_uniform_ambient_cover_bound D hc hn hsec (incl p)
    incl hincl.continuous.measurable hinside gL.volumeMeasure
    (fun x:L => max 0 (gL.leviCivitaData.scalarCurvature x)) K hRi hKi
    (fun _ => le_max_left _ _) hKn hr hr1 hB hbound

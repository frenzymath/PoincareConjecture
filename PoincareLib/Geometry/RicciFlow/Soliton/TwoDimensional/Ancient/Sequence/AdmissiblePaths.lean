import PoincareLib.Geometry.RicciFlow.AncientKappa.Basic
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution.BoundaryRegularity
import PoincareLib.Geometry.RicciFlow.Harnack.Regularity
import PoincareLib.Geometry.Riemannian.Distance.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Admissible backward paths on ancient surfaces

A globally C1 connecting curve has continuous backward L-integrand on each
closed finite time interval. This supplies an actual finite competitor in
the definition of reduced length, without a reduced-geometry service.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareMT

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

namespace RicciFlow

/-- The backward L-integrand of a globally C1 curve is continuous on each
closed backward-time interval of an ancient surface flow. -/
theorem continuousOn_backwardLIntegrand_surface_of_contMDiff
    (F : RicciFlow 2 M (Iic 0)) {tau : ℝ} (htau : 0 < tau)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 γ) :
    ContinuousOn (backwardLIntegrand F 0 γ) (Icc 0 tau) := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 0
      (fun s : ℝ => (⟨s, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro s
    simp only [contMDiffAt_totalSpace, trivializationAt_model_space_apply]
    exact ⟨contMDiffAt_id, contMDiffAt_const⟩
  have hv := (hγ.contMDiff_tangentMap (m := 0) (by simp)).comp hunit
  have hparam : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 2)) 0
      (fun s : ℝ => (0 - s, γ s)) :=
    (contMDiff_const.sub contMDiff_id).prodMk (hγ.of_le (by simp))
  have hg := (F.smooth.of_le (show (0 : WithTop ℕ∞) ≤ ∞ by simp)).comp
    hparam.contMDiffOn (fun s (hs : s ∈ Icc 0 tau) =>
      show (0 - s, γ s) ∈ Iic (0 : ℝ) ×ˢ (univ : Set M) from
        ⟨by simpa using neg_nonpos.mpr hs.1, mem_univ _⟩)
  have heval := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    hv.contMDiffOn hv.contMDiffOn
  have henergy : ContinuousOn (fun s => (F.metric (0 - s)).inner (γ s)
      (curveVelocity γ s) (curveVelocity γ s)) (Icc 0 tau) := by
    intro s hs
    have h := heval s hs
    exact (contMDiffWithinAt_totalSpace.mp h).2.continuousWithinAt
  have hab : -tau < 0 := by linarith
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Icc (-tau) 0 ⊆ Iic 0 from fun _ hs => hs.2) ordConnected_Icc
    ⟨-tau, ⟨le_rfl, hab.le⟩, 0, ⟨hab.le, le_rfl⟩, hab.ne⟩
  have hscalar : ContinuousOn (fun s => (F.connection (0 - s)).scalarCurvature (γ s))
      (Icc 0 tau) := by
    change ContinuousOn ((fun p : ℝ × M => (G.connection p.1).scalarCurvature p.2) ∘
      fun s : ℝ => (0 - s, γ s)) (Icc 0 tau)
    exact (G.contMDiffOn_scalarCurvature_surface_Icc hab).continuousOn.comp
      (f := fun s : ℝ => (0 - s, γ s)) hparam.continuous.continuousOn
      (fun s hs => ⟨by constructor <;> linarith [hs.1, hs.2], mem_univ _⟩)
  exact Real.continuous_sqrt.continuousOn.mul (hscalar.add henergy)

/-- Every globally C1 curve has finite backward L-action on a finite ancient
surface time interval. -/
theorem intervalIntegrable_backwardLIntegrand_surface_of_contMDiff
    (F : RicciFlow 2 M (Iic 0)) {tau : ℝ} (htau : 0 < tau)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 γ) :
    IntervalIntegrable (backwardLIntegrand F 0 γ) volume 0 tau :=
  (F.continuousOn_backwardLIntegrand_surface_of_contMDiff htau hγ).intervalIntegrable_of_Icc
    htau.le

end RicciFlow

namespace AncientKappaSolution

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

/-- Between arbitrary endpoints, an ancient surface kappa-solution has an
actual backward-time path of finite L-action. -/
theorem exists_backwardTimePath_surface (K : AncientKappaSolution 2 M)
    (p q : M) {tau : ℝ} (htau : 0 < tau) :
    ∃ path : BackwardTimePath K.flow 0 0 tau, path.curve 0 = p ∧ path.curve tau = q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨(K.flow.metric 0).toRiemannianMetric⟩
  have hfinite : Manifold.riemannianEDist (𝓡 2) p q < ⊤ :=
    lt_top_iff_ne_top.mpr ((K.flow.metric 0).edist_ne_top p q)
  obtain ⟨γ, hγp, hγq, hγ, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hfinite htau
  refine ⟨{
    curve := γ
    nonnegative := le_rfl
    ordered := htau
    terminal_mem := by simp
    time_mem := fun s hs => by simpa using neg_nonpos.mpr hs.1
    continuous := hγ.continuous.continuousOn
    regular := hγ.contMDiffOn
    l_integrable := K.flow.intervalIntegrable_backwardLIntegrand_surface_of_contMDiff htau hγ
  }, hγp, hγq⟩

end AncientKappaSolution

end PoincareMT

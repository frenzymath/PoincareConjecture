import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.ProductIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Components

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

structure GlobalParallelPotential (D : LeviCivitaData g) where
  coordinate : M → ℝ
  coordinate_smooth : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ coordinate
  coordinate_unit : RiemannianMetric.HasUnitGradient D coordinate
  coordinate_zero_hessian : RiemannianMetric.HasZeroHessian D coordinate

theorem global_parallel_product_isometry
    {D : LeviCivitaData g} (P : GlobalParallelPotential D)
    (hc : MetricComplete g) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace P.coordinate_smooth (⊤ : Opens M)
      (fun x _ => RiemannianMetric.regular_of_hasUnitGradient P.coordinate_unit x) 2 0
    letI := isManifold_openLevelSet P.coordinate_smooth (⊤ : Opens M)
      (fun x _ => RiemannianMetric.regular_of_hasUnitGradient P.coordinate_unit x) 2 0
    let h := RiemannianMetric.regularLevelMetric P.coordinate_smooth (⊤ : Opens M)
      (fun x _ => RiemannianMetric.regular_of_hasUnitGradient P.coordinate_unit x) 0 g
    Nonempty (RiemannianMetric.zeroLevelSet P.coordinate) ∧
      ConnectedSpace (RiemannianMetric.zeroLevelSet P.coordinate) ∧ MetricComplete h ∧
      ∃ Φ : ℝ → M → M,
        ∃ e : (RiemannianMetric.zeroLevelSet P.coordinate × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ M,
          (∀ x, Φ 0 x = x) ∧
          (∀ x, IsMIntegralCurve (fun t => Φ t x) (D.gradient P.coordinate)) ∧
          ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
            (fun z : ℝ × M => Φ z.1 z.2) ∧
          (∀ z, e z = Φ z.2 (RiemannianMetric.zeroLevelIncl P.coordinate z.1)) ∧
          (∀ z, P.coordinate (e z) = z.2) ∧
          (∀ (z : RiemannianMetric.zeroLevelSet P.coordinate × ℝ)
              (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
            g.inner (e z)
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
              h.inner z.1 v.1 w.1 + v.2 * w.2) ∧
          (∀ x, (e.symm x).2 = P.coordinate x) ∧
          (∀ x, RiemannianMetric.zeroLevelIncl P.coordinate (e.symm x).1 =
            Φ (-P.coordinate x) x) := by
  exact RiemannianMetric.exists_parallelGradient_productIsometry
    hc P.coordinate_smooth P.coordinate_unit P.coordinate_zero_hessian

end PoincareConjecture.RicciFlow.Splitting

namespace PoincareConjecture.RicciFlow.Splitting

open RiemannianMetric

theorem exists_connectedComponent_productIsometry
    {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hu : HasUnitGradient D f) (hz : HasZeroHessian D f)
    (hc : MetricComplete g) (p : M) :
    let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
    let gC := g.connectedComponentMetric p
    ∃ (N : Type u) (_ : TopologicalSpace N) (_ : T3Space N)
      (_ : ConnectedSpace N) (_ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) N)
      (_ : IsManifold (𝓡 2) ∞ N) (h : RiemannianMetric 2 N),
      MetricComplete h ∧
      ∃ e : (N × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ C,
        (∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          gC.inner (e z) (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
              h.inner z.1 v.1 w.1 + v.2 * w.2) ∧
        (∀ x, (e.symm x).2 = f x.1) := by
  let C := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) p
  let gC := g.connectedComponentMetric p
  let fC : C → ℝ := f ∘ Subtype.val
  obtain ⟨hconn, hcomp, hfs, hus, hzs⟩ :=
    connectedComponent_complete_parallel_coordinate D hf hu hz hc p
  let : ConnectedSpace C := hconn
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hreg := fun x (_ : x ∈ (⊤ : Opens C)) => regular_of_hasUnitGradient hus x
  let := openLevelSetChartedSpace hfs (⊤ : Opens C) hreg 2 0
  let := isManifold_openLevelSet hfs (⊤ : Opens C) hreg 2 0
  let h := regularLevelMetric hfs (⊤ : Opens C) hreg 0 gC
  obtain ⟨_, hconnected, hcomplete, Φ, e, _, _, _, _, _, hm, hcoord, _⟩ :=
    exists_parallelGradient_productIsometry hcomp hfs hus hzs
  exact ⟨zeroLevelSet fC, inferInstance, inferInstance, hconnected,
    inferInstance, inferInstance, h, hcomplete, e, hm, hcoord⟩

end PoincareConjecture.RicciFlow.Splitting

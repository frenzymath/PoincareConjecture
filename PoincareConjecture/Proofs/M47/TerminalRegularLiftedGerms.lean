import PoincareConjecture.Proofs.M47.TerminalGermsUniverseMetric
import PoincareConjecture.Proofs.M47.TerminalGermsOpenReadout
import PoincareConjecture.Proofs.M47.TerminalGermsExhaustionOperator
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalSource_regular_lifted_germs
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T3Space X]
    (g : RiemannianMetric 3 X) (hg : MetricComplete g)
    {ι : Type*} (U : ι → Opens X) [∀ i, ConnectedSpace (U i)]
    (tau : ι → ℝ) (htau : ∀ i, 0 < tau i)
    (F : ∀ i, RicciFlow 3 (U i) (Icc (-tau i) 0))
    (hmetric : ∀ i (x : U i) (v w : TangentSpace (𝓡 3) x),
      ((F i).metric 0).inner x v w = g.inner x.val v w)
    (hoperator : ∀ i t, t ∈ Icc (-tau i) 0 → ∀ x,
      ((F i).connection t).NonnegativeCurvatureOperator x)
    (htriple : ∀ x y z : X, ∃ i, x ∈ U i ∧ y ∈ U i ∧ z ∈ U i) :
    letI : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
    letI : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
    let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
    let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
    let UL := fun i => terminalGermsOpenChartSource d d.isLocalDiffeomorph (U i)
    MetricComplete gL ∧ (∀ i, ConnectedSpace (UL i)) ∧
      ∃ FL : ∀ i, RicciFlow 3 (UL i) (Icc (-tau i) 0),
        (∀ i (x : UL i) (v w : TangentSpace (𝓡 3) x),
          ((FL i).metric 0).inner x v w = gL.inner x.val v w) ∧
        (∀ i t, t ∈ Icc (-tau i) 0 → ∀ x,
          ((FL i).connection t).NonnegativeCurvatureOperator x) ∧
        (∀ x y z : ULift.{u} X, ∃ i, x ∈ UL i ∧ y ∈ UL i ∧ z ∈ UL i) ∧
        ∀ DL : LeviCivitaData gL, ∀ x, DL.NonnegativeCurvatureOperator x := by
  let : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
  let : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
  let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
  let UL := fun i => terminalGermsOpenChartSource d d.isLocalDiffeomorph (U i)
  let q := fun i => terminalGermsOpenChartMap d d.isLocalDiffeomorph (U i)
  have hq (i : ι) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (q i) :=
    terminalGerms_openChartMap_localDiffeomorph d d.isLocalDiffeomorph (U i)
  let FL := fun i => (F i).pullbackWithConnection (q i) (hq i)
    (fun t => ((F i).metric t).pullbackOfLocalDiffeomorph (q i) (hq i) |>.leviCivitaData)
  have hconnected (i : ι) : ConnectedSpace (UL i) := by
    apply isConnected_iff_connectedSpace.mp
    exact d.toHomeomorph.isConnected_preimage.mpr
      (isConnected_iff_connectedSpace.mpr inferInstance)
  have hm (i : ι) (x : UL i) (v w : TangentSpace (𝓡 3) x) :
      ((FL i).metric 0).inner x v w = gL.inner x.val v w := by
    change ((F i).metric 0).inner (q i x)
      (mfderiv (𝓡 3) (𝓡 3) (q i) x v)
      (mfderiv (𝓡 3) (𝓡 3) (q i) x w) = _
    rw [hmetric, terminalGerms_openChartMap_mfderiv]
    rfl
  have hop (i : ι) (t : ℝ) (ht : t ∈ Icc (-tau i) 0) (x : UL i) :
      ((FL i).connection t).NonnegativeCurvatureOperator x := by
    apply (((FL i).connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
      ((F i).connection t) (f := q i) isOpen_univ (hq i).contMDiff.contMDiffOn
      (fun _ _ _ _ => rfl) (mem_univ x)).mpr
    exact hoperator i t ht (q i x)
  have htr (x y z : ULift.{u} X) : ∃ i, x ∈ UL i ∧ y ∈ UL i ∧ z ∈ UL i :=
    htriple x.down y.down z.down
  refine ⟨(terminalGerms_lifted_complete_metric g hg).1, hconnected, FL, hm, hop, htr, ?_⟩
  intro DL
  apply terminalGerms_ambient_operator_of_exhaustion DL UL tau htau FL hm hop
  intro x
  obtain ⟨i, hi, _, _⟩ := htr x x x
  exact ⟨i, hi⟩

theorem terminalSource_regular_lifted_curvature
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] {g : RiemannianMetric 3 X} (D : LeviCivitaData g) :
    letI : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
    letI : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
    let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
    let gL := g.pullbackOfLocalDiffeomorph d d.isLocalDiffeomorph
    ∀ DL : LeviCivitaData gL, ∀ x : ULift.{u} X,
      DL.scalarCurvature x = D.scalarCurvature x.down ∧
        DL.curvatureTensorNorm x = D.curvatureTensorNorm x.down := by
  let : ChartedSpace E (ULift.{u} X) := Poincare.Manifold.uliftChartedSpace E X
  let : IsManifold (𝓡 3) ∞ (ULift.{u} X) := Poincare.Manifold.uliftIsManifold (𝓡 3) X
  let d := Poincare.Manifold.uliftDiffeomorph (𝓡 3) X
  dsimp only
  intro DL x
  exact ⟨DL.scalarCurvature_eq_of_local_isometry D (f := d) isOpen_univ
      d.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x),
    DL.curvatureTensorNorm_eq_of_local_isometry D (f := d) isOpen_univ
      d.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)⟩

end PoincareConjecture.M47

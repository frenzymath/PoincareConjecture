import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.UnitCover












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}








structure NullOrientationCover (D : LeviCivitaData g) where
  covering : IsCoveringMap (unitRicciKernelProjection D)
  fiber_card : ∀ x : M,
    Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2
  deck : UnitRicciKernel D ≃ₜ UnitRicciKernel D
  deck_involutive : Function.Involutive deck
  deck_projection : ∀ p,
    unitRicciKernelProjection D (deck p) = unitRicciKernelProjection D p
  deck_free : ∀ p, deck p ≠ p

omit [T2Space M] [ConnectedSpace M] in
@[simp] theorem NullOrientationCover.deck_projection_apply
    {D : LeviCivitaData g} (C : NullOrientationCover D)
    (p : UnitRicciKernel D) :
    unitRicciKernelProjection D (C.deck p) = unitRicciKernelProjection D p :=
  C.deck_projection p

theorem nullOrientationCover_of_terminal_null_plane
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hnonflat : ∃ p, (F.connection 0).curvatureTensorNorm p ≠ 0)
    (x : M) (v w : TangentSpace (𝓡 3) x)
    (hv : (F.metric 0).inner x v v = 1)
    (hw : (F.metric 0).inner x w w = 1)
    (hvw : (F.metric 0).inner x v w = 0)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    Nonempty (NullOrientationCover (F.connection 0)) := by
  obtain ⟨hcover, hcard⟩ :=
    PoincareConjecture.RicciFlow.unitRicciKernel_doubleCover_of_terminal_null_plane
      hC F hoperator hnonflat x v w hv hw hvw hzero
  let D := F.connection 0
  let deck := unitRicciKernelDeckHomeomorph D
  exact ⟨{
    covering := hcover
    fiber_card := hcard
    deck := deck
    deck_involutive := unitRicciKernelReverse_involutive D
    deck_projection := fun p => unitRicciKernelProjection_reverse D p
    deck_free := unitRicciKernelReverse_fixedPointFree D
  }⟩

end PoincareConjecture.RicciFlow.Splitting

import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinarySquareEuler
import PoincareConjecture.Proofs.M34.Standard.SquareInitialValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M34

variable {n : ℕ} {I : SpacetimeInterval}
  {F : RicciFlow n (EuclideanSpace ℝ (Fin n)) I.domain}

set_option backward.isDefEq.respectTransparency false in

theorem ordinaryProduct_positive_survival
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    {T taumax tau : ℝ} (L : LGeodesicTheory F T taumax) (hT : T ∈ I.domain)
    (htau : 0 < tau) (hmax : tau ≤ taumax) (p : EuclideanSpace ℝ (Fin n))
    (E : M14ExponentialFamily (ordinaryProductLGeometry R hRicci) T
      (R.product.productCylinder.toSpacetime (⟨T, hT⟩, p))) :
    ∃ Z, (Z, Real.sqrt tau) ∈ E.domain := by
  obtain ⟨q, hq0, _, hqmin⟩ := L.minimizing_existence 0 tau le_rfl htau hmax p p
  obtain ⟨A⟩ := L.regularized_geodesic 0 tau le_rfl htau hmax q
    (L.euler_lagrange 0 tau le_rfl htau hmax q hqmin)
  obtain ⟨Z, hZ⟩ := exists_squareInitialValue_of_euler (ordinaryLiftedPath R hRicci q)
    (ordinarySquarePath R hRicci q A.path) (ordinarySquareExtension R hRicci q A.path)
    (fun _ hs W => ordinarySquarePath_euler R hRicci q A hs W)
  let xq : (ordinaryProductLGeometry R hRicci).Point :=
    R.product.productCylinder.toSpacetime
      (⟨T - 0, q.time_mem 0 ⟨le_rfl, q.ordered.le⟩⟩, q.curve 0)
  have H : ∃ (Z : (ordinaryProductLGeometry R hRicci).Horizontal xq)
      (y : (ordinaryProductLGeometry R hRicci).Point),
      Nonempty (M14SquareRootInitialValuePath (ordinaryProductLGeometry R hRicci)
        T tau xq y Z) := ⟨Z, _, hZ⟩
  have hx : xq = R.product.productCylinder.toSpacetime (⟨T, hT⟩, p) := by
    apply congrArg R.product.productCylinder.toSpacetime
    exact Prod.ext (Subtype.ext (sub_zero T)) hq0
  rw [hx] at H
  obtain ⟨Z, y, hy⟩ := H
  refine ⟨Z, (E.positive_survival_iff Z (Real.sqrt tau) (Real.sqrt_pos.mpr htau)).mpr ?_⟩
  simpa only [Real.sq_sqrt htau.le] using (show ∃ y,
    Nonempty (M14SquareRootInitialValuePath (ordinaryProductLGeometry R hRicci)
      T tau (R.product.productCylinder.toSpacetime (⟨T, hT⟩, p)) y Z) from ⟨y, hy⟩)

theorem ordinaryProduct_stableSet
    (R : OrdinaryProductRicciGeometry F.metric I)
    (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
    (C : M14ExponentialConclusion (ordinaryProductLGeometry R hRicci))
    {T taumax tau : ℝ} (L : LGeodesicTheory F T taumax) (hT : T ∈ I.domain)
    (htau : 0 < tau) (hmax : tau ≤ taumax) (p : EuclideanSpace ℝ (Fin n)) :
    ∃ E : M14ExponentialFamily (ordinaryProductLGeometry R hRicci) T
      (R.product.productCylinder.toSpacetime (⟨T, hT⟩, p)),
      Nonempty (M14StableSet (ordinaryProductLGeometry R hRicci) T tau
        (R.product.productCylinder.toSpacetime (⟨T, hT⟩, p)) E) := by
  have hbase : (ordinaryProductLGeometry R hRicci).spacetime.timeFunction
      (R.product.productCylinder.toSpacetime (⟨T, hT⟩, p)) = T :=
    R.product.productCylinder.time_eq _
  obtain ⟨E⟩ := C.family T _ hbase
  exact ⟨E, C.stable T tau _ hbase htau E
    (ordinaryProduct_positive_survival R hRicci L hT htau hmax p E)⟩

end PoincareConjecture.M34

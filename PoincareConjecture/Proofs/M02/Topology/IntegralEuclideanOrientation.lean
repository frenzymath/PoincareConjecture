import PoincareConjecture.Proofs.M02.Topology.IntegralManifoldOrientation
import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupport



set_option autoImplicit false

noncomputable section

open Set TopologicalSpace

namespace PoincareConjecture.Proofs.M02.Topology

abbrev integralEuclideanSpace := EuclideanSpace Real (Fin 3)

theorem integralEuclideanSupportDetected :
    ∀ L : Set integralEuclideanSpace, IsCompact L → IntegralSupportDetected L 3 :=
  fun L hL => integralEuclideanCompactSupportThree_detected L hL

theorem exists_integralEuclideanOrientationData :
    ∃ (omega : ∀ x : integralEuclideanSpace,
      integralSupportHomology ({x} : Set integralEuclideanSpace) 3),
      (∀ x, ∃ e : Int ≃ₗ[Int]
        integralSupportHomology ({x} : Set integralEuclideanSpace) 3, e 1 = omega x) ∧
      (∀ x : integralEuclideanSpace, ∃ U : Set integralEuclideanSpace, IsOpen U ∧ x ∈ U ∧
        ∃ b : integralSupportHomology U 3,
          ∀ y : integralEuclideanSpace, ∀ hy : y ∈ U,
            integralSupportHomologyRestriction (singleton_subset_iff.mpr hy) 3 b = omega y) := by
  simpa only [integralEuclideanSpace] using
    (exists_integralThreeLocallyRepresentedGenerators
      (X := integralEuclideanSpace) (0 : integralEuclideanSpace))

end PoincareConjecture.Proofs.M02.Topology

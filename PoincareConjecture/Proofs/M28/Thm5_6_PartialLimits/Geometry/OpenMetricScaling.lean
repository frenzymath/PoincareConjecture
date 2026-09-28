import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicOpenMetric
import PoincareConjecture.Proofs.M13.Metric
import PoincareConjecture.Proofs.M13.Length










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]




theorem intrinsicOpenMetric_scaleSmoothMetric_edist
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (Q : ℝ) (hQ : 0 < Q) (p q : U) :
    (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U).edist p q =
      ENNReal.ofReal (Real.sqrt Q) * (intrinsicOpenMetric g U).edist p q := by
  have hh : MetricHomothety (intrinsicOpenMetric g U)
      (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U)
      (Diffeomorph.refl (𝓡 3) U ∞) Q := by
    intro x v w
    change (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U).inner x
      (mfderiv (𝓡 3) (𝓡 3) (id : U → U) x v)
      (mfderiv (𝓡 3) (𝓡 3) (id : U → U) x w) =
        Q * (intrinsicOpenMetric g U).inner x v w
    rw [mfderiv_id]
    simp only [intrinsicOpenMetric_inner, M13.scaleSmoothMetric_inner]
    rfl
  exact M13.homothety_edist (intrinsicOpenMetric g U)
    (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U)
    (Diffeomorph.refl (𝓡 3) U ∞) Q hQ hh p q




theorem intrinsicOpenMetric_scaleSmoothMetric_edist_toReal
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (Q : ℝ) (hQ : 0 < Q) (p q : U) :
    ((intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U).edist p q).toReal =
      Real.sqrt Q * ((intrinsicOpenMetric g U).edist p q).toReal := by
  rw [intrinsicOpenMetric_scaleSmoothMetric_edist, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg Q)]

end PoincareConjecture.M28

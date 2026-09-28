import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Model
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.TensorNorm


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle BigOperators
namespace PoincareConjecture

def roundCylinderChartFrame (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    (a : Fin 3) :
    RoundCylinderTangent ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2) :=
  (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1
    (roundCylinderCoordinateBasis a).1, (roundCylinderCoordinateBasis a).2)

theorem roundCylinderChartFrame_gram (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    (a b : Fin 3) :
    roundCylinderProductMetric.inner
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)
      (roundCylinderChartFrame q p a) (roundCylinderChartFrame q p b) =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b := by
  rw [roundCylinderProductMetric_inner]
  rfl

theorem roundCylinderChartFrame_linearIndependent (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) : LinearIndependent ℝ (roundCylinderChartFrame q p) := by
  let : Bundle.RiemannianBundle (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
    ⟨roundCylinderProductMetric.toRiemannianMetric⟩
  apply Matrix.det_gram_ne_zero_iff_linearIndependent.mp
  have hGram : Matrix.gram ℝ (roundCylinderChartFrame q p) =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p := by
    ext a b
    exact roundCylinderChartFrame_gram q p a b
  rw [hGram]
  exact roundCylinderGram_det_ne_zero (by norm_num) q p

def roundCylinderChartBasis (q : UnitTwoSphere) (p : RoundCylinderCoordinates) :
    Module.Basis (Fin 3) ℝ
      (RoundCylinderTangent ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) :=
  basisOfLinearIndependentOfCardEqFinrank (roundCylinderChartFrame_linearIndependent q p)
    (by change 3 = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ); simp)

@[simp] theorem roundCylinderChartBasis_apply (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (a : Fin 3) :
    roundCylinderChartBasis q p a = roundCylinderChartFrame q p a :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) a

end PoincareConjecture

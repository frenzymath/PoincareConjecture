import PoincareConjecture.Proofs.M34.Mathlib.SphereChartMetric
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderPullback
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.StereographicMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff RealInnerProductSpace EuclideanSpace

namespace PoincareConjecture.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

noncomputable def cylinderHorizontal : E3 →L[ℝ] E2 :=
  (EuclideanSpace.proj 0).smulRight (EuclideanSpace.single 0 1) +
    (EuclideanSpace.proj 1).smulRight (EuclideanSpace.single 1 1)

theorem cylinderHorizontal_apply (x : E3) :
    cylinderHorizontal x = WithLp.toLp 2 ![x 0, x 1] := by
  ext i
  fin_cases i <;> simp [cylinderHorizontal]

theorem cylinderHorizontal_norm_sq (x : E3) :
    ‖cylinderHorizontal x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp [cylinderHorizontal_apply]

theorem cylinderHorizontal_inner (u v : E3) :
    inner ℝ (cylinderHorizontal u) (cylinderHorizontal v) = u 0 * v 0 + u 1 * v 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two, cylinderHorizontal_apply]
  ring

noncomputable def sphereCylinderChart (q : UnitTwoSphere) (x : E3) : StandardCylinderSpace :=
  ((chartAt E2 q).symm (cylinderHorizontal x), x 2)

theorem sphereCylinderChart_contMDiff (q : UnitTwoSphere) :
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (sphereCylinderChart q) := by
  exact ((contMDiff_sphere_chart_symm (n := 2) q).comp
    cylinderHorizontal.contDiff.contMDiff).prodMk
    (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ).contDiff.contMDiff

theorem sphereCylinderChart_mfderiv (q : UnitTwoSphere) (x u : E3) :
    mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (sphereCylinderChart q) x u =
      (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 q).symm
        (cylinderHorizontal x) (cylinderHorizontal u), u 2) := by
  have hh0 : ContMDiff (𝓡 3) (𝓡 2) ∞ cylinderHorizontal :=
    cylinderHorizontal.contDiff.contMDiff
  have hh := hh0.mdifferentiable (by simp)
  have hs := (contMDiff_sphere_chart_symm (n := 2) (m := ∞) q).mdifferentiable (by simp)
  have ha0 : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ) :=
    (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ).contDiff.contMDiff
  have ha := ha0.mdifferentiable (by simp)
  have hc := mfderiv_comp x (hs (cylinderHorizontal x)) (hh x)
  rw [mfderiv_eq_fderiv, cylinderHorizontal.fderiv] at hc
  change mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ))
    (fun y => (((chartAt E2 q).symm ∘ cylinderHorizontal) y, EuclideanSpace.proj 2 y)) x u = _
  rw [mfderiv_prodMk ((hs _).comp x (hh x)) (ha x)]
  change (mfderiv (𝓡 3) (𝓡 2) ((chartAt E2 q).symm ∘ cylinderHorizontal) x u,
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ) x u) = _
  rw [hc, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

theorem standardCylinderInner_sphereCylinderChart (q : UnitTwoSphere) (t : ℝ)
    (x u v : E3) :
    standardCylinderInner t (sphereCylinderChart q x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (sphereCylinderChart q) x u)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (sphereCylinderChart q) x v) =
        stereographicCylinderCoefficients (2 * (1 - t)) x u v := by
  rw [sphereCylinderChart_mfderiv, sphereCylinderChart_mfderiv]
  change 2 * (1 - t) *
    @inner ℝ E3 _
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1)
        ((chartAt E2 q).symm (cylinderHorizontal x))
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 q).symm
          (cylinderHorizontal x) (cylinderHorizontal u)))
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => z.1)
        ((chartAt E2 q).symm (cylinderHorizontal x))
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E2 q).symm
          (cylinderHorizontal x) (cylinderHorizontal v))) + u 2 * v 2 = _
  rw [inner_mfderiv_sphere_chart_symm, cylinderHorizontal_inner,
    stereographicCylinderCoefficients_apply]
  have hd : ‖cylinderHorizontal x‖ ^ 2 + 4 = stereographicCylinderDenominator x := by
    rw [cylinderHorizontal_norm_sq]
    dsimp only [stereographicCylinderDenominator]
    ring
  rw [hd]
  simp only [stereographicCylinderDensity, mul_assoc]

variable {g : RiemannianMetric 3 StandardCapSpace}

noncomputable def endStereographicChart (e : StandardCylindricalEnd g)
    (q : UnitTwoSphere) (x : E3) : StandardCapSpace :=
  e.coordinate (sphereCylinderChart q x)

theorem endStereographicChart_contMDiffAt (e : StandardCylindricalEnd g)
    (q : UnitTwoSphere) {x : E3} (hx : 0 < x 2) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (endStereographicChart e q) x :=
  (end_coordinate_contMDiffAt e hx).comp x (sphereCylinderChart_contMDiff q x)

theorem endStereographicChart_mfderiv (e : StandardCylindricalEnd g)
    (q : UnitTwoSphere) {x : E3} (hx : 0 < x 2) (u : E3) :
    mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) x u =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate (sphereCylinderChart q x)
        (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (sphereCylinderChart q) x u) := by
  have hc := mfderiv_comp x
    ((end_coordinate_contMDiffAt e hx).mdifferentiableAt (by simp))
    ((sphereCylinderChart_contMDiff q x).mdifferentiableAt (by simp))
  exact congrArg (fun L => L u) hc

theorem endExhaustion_fderiv_stereographic (e : StandardCylindricalEnd g)
    (q : UnitTwoSphere) {x : E3} (hx : 2 < x 2) (u : E3) :
    fderiv ℝ (endExhaustion e) (endStereographicChart e q x)
      (mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) x u) = u 2 := by
  rw [endStereographicChart_mfderiv e q (by linarith)]
  change fderiv ℝ (endExhaustion e) (e.coordinate (sphereCylinderChart q x))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate (sphereCylinderChart q x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (sphereCylinderChart q) x u)) = _
  rw [endExhaustion_fderiv_coordinate e hx, sphereCylinderChart_mfderiv]

theorem endCylinderAuxMetric_stereographic (e : StandardCylindricalEnd g)
    (q : UnitTwoSphere) (t : ℝ) {x : E3} (hx : 2 < x 2) (u v : E3) :
    (endCylinderAuxMetric e t).inner (endStereographicChart e q x)
      (mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) x u)
      (mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) x v) =
        stereographicCylinderCoefficients (2 * (1 - endCylinderParameter t)) x u v := by
  have hc := mfderiv_comp x
    ((end_coordinate_contMDiffAt e (by change 0 < x 2; linarith)).mdifferentiableAt
      (by simp))
    ((sphereCylinderChart_contMDiff q x).mdifferentiableAt (by simp))
  change mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) x = _ at hc
  rw [hc]
  change (endCylinderAuxMetric e t).inner (e.coordinate (sphereCylinderChart q x))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate (sphereCylinderChart q x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (sphereCylinderChart q) x u))
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e.coordinate (sphereCylinderChart q x)
      (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (sphereCylinderChart q) x v)) = _
  rw [endCylinderAuxMetric_coordinate e t hx]
  exact standardCylinderInner_sphereCylinderChart q (endCylinderParameter t) x u v

end PoincareConjecture.M34

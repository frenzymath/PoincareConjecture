import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderCharts
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.StereographicCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 3 StandardCapSpace}

theorem endCylinderAuxRicci_stereographic (e : StandardCylindricalEnd g) (t : ℝ)
    (D : LeviCivitaData (endCylinderAuxMetric e t)) (q : UnitTwoSphere)
    {x : E3} (hx : 2 < x 2) (u v : E3) :
    D.ricci (endStereographicChart e q x)
      (mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) x u)
      (mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) x v) =
        stereographicCylinderDensity x * (u 0 * v 0 + u 1 * v 1) := by
  have hb : 0 < 2 * (1 - endCylinderParameter t) := by
    linarith [endCylinderParameter_lt_one t]
  let G := stereographicCylinderMetric (2 * (1 - endCylinderParameter t)) hb
  let DG := G.euclideanLeviCivitaData
  have hU : IsOpen {y : E3 | 2 < y 2} :=
    isOpen_lt continuous_const (EuclideanSpace.proj 2 : E3 →L[ℝ] ℝ).continuous
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (endStereographicChart e q) {y : E3 | 2 < y 2} := by
    intro y hy
    change 2 < y 2 at hy
    exact (endStereographicChart_contMDiffAt e q (by linarith)).contMDiffWithinAt
  have hm : ∀ y ∈ {y : E3 | 2 < y 2}, ∀ u v : TangentSpace (𝓡 3) y,
      G.inner y u v = (endCylinderAuxMetric e t).inner (endStereographicChart e q y)
        (mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) y u)
        (mfderiv (𝓡 3) (𝓡 3) (endStereographicChart e q) y v) := by
    intro y hy u v
    exact (endCylinderAuxMetric_stereographic e q t hy u v).symm
  exact (DG.ricci_eq_of_local_isometry D hU hf hm hx u v).symm.trans
    (stereographicCylinderRicci hb DG x u v)

theorem endCylinderAuxRicci_at_stereographic (e : StandardCylindricalEnd g) (t : ℝ)
    (D : LeviCivitaData (endCylinderAuxMetric e t)) (q : UnitTwoSphere)
    {x : E3} (hx : 2 < x 2) (u v : E3) :
    D.ricci (endStereographicChart e q x) u v =
      (g.inner (endStereographicChart e q x) u v -
        fderiv ℝ (endExhaustion e) (endStereographicChart e q x) u *
          fderiv ℝ (endExhaustion e) (endStereographicChart e q x) v) / 2 := by
  have hb : 0 < 2 * (1 - endCylinderParameter t) := by
    linarith [endCylinderParameter_lt_one t]
  let G := stereographicCylinderMetric (2 * (1 - endCylinderParameter t)) hb
  have hbij := G.mfderiv_bijective_of_pullback_eq (endCylinderAuxMetric e t) x
    (fun a b => endCylinderAuxMetric_stereographic e q t hx a b)
  obtain ⟨a, rfl⟩ := hbij.2 u
  obtain ⟨b, rfl⟩ := hbij.2 v
  rw [endCylinderAuxRicci_stereographic e t D q hx,
    endExhaustion_fderiv_stereographic e q hx, endExhaustion_fderiv_stereographic e q hx]
  have hm := endCylinderAuxMetric_stereographic e q 0 hx a b
  rw [endCylinderAuxMetric_zero, show endCylinderParameter 0 = 0 by
    simp [endCylinderParameter], stereographicCylinderCoefficients_apply] at hm
  rw [hm]
  ring

theorem endCylinderAuxRicci_coordinate (e : StandardCylindricalEnd g) (t : ℝ)
    (D : LeviCivitaData (endCylinderAuxMetric e t))
    {z : StandardCylinderSpace} (hz : 2 < z.2) (u v : E3) :
    D.ricci (e.coordinate z) u v =
      (g.inner (e.coordinate z) u v - fderiv ℝ (endExhaustion e) (e.coordinate z) u *
        fderiv ℝ (endExhaustion e) (e.coordinate z) v) / 2 := by
  let c := chartAt E2 z.1
  let y : E3 := WithLp.toLp 2 ![(c z.1) 0, (c z.1) 1, z.2]
  have hh : cylinderHorizontal y = c z.1 := by
    ext i
    fin_cases i <;> simp [cylinderHorizontal_apply, y]
  have hy : sphereCylinderChart z.1 y = z := by
    apply Prod.ext
    · change c.symm (cylinderHorizontal y) = z.1
      rw [hh]
      exact c.left_inv (mem_chart_source E2 z.1)
    · rfl
  have hx : endStereographicChart e z.1 y = e.coordinate z := congrArg e.coordinate hy
  have h := endCylinderAuxRicci_at_stereographic e t D z.1
    (show 2 < y 2 from hz) u v
  exact (congrArg (fun p : E3 => D.ricci p u v =
    (g.inner p u v - fderiv ℝ (endExhaustion e) p u *
      fderiv ℝ (endExhaustion e) p v) / 2) hx).mp h

end PoincareConjecture.M34

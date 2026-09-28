import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.ConstantLift
import PoincareConjecture.Proofs.M60.Def18_17_FillingArea.BoundaryCurveLipschitz

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

def auxiliaryCircleFiber (P : M62.CircleProductData F circumference)
    (x : M) : ℝ → P.charts.Point := fun s => (x, P.circle.quotient s)

theorem auxiliaryCircle_fiber_contMDiff
    (P : M62.CircleProductData F circumference) (x : M) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ (auxiliaryCircleFiber P x) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  exact P.charts.from_product_smooth.comp
    (contMDiff_const.prodMk P.circle.quotient_smooth)

theorem auxiliaryCircle_fiber_velocity_split
    (P : M62.CircleProductData F circumference) (x : M) (s : ℝ) :
    P.charts.split (auxiliaryCircleFiber P x s)
      (curveVelocity (auxiliaryCircleFiber P x) s) =
        (0, curveVelocity P.circle.quotient s) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hF := (auxiliaryCircle_fiber_contMDiff P x).mdifferentiableAt (x := s) (by simp)
  apply Prod.ext
  · rw [P.charts.split_space]
    have h := mfderiv_comp_apply (f := auxiliaryCircleFiber P x)
      (g := (Prod.fst : P.charts.Point → M)) s
      ((contMDiff_fst.comp P.charts.to_product_smooth).mdifferentiableAt (by simp)) hF 1
    have hc : (Prod.fst : P.charts.Point → M) ∘ auxiliaryCircleFiber P x =
        fun _ => x := rfl
    rw [hc, mfderiv_const] at h
    exact h.symm
  · rw [P.charts.split_circle]
    have h := mfderiv_comp_apply (f := auxiliaryCircleFiber P x)
      (g := (Prod.snd : P.charts.Point → P.circle.Point)) s
      ((contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiableAt (by simp)) hF 1
    exact h.symm

theorem auxiliaryCircle_fiber_speed
    (P : M62.CircleProductData F circumference) (time : ℝ) (x : M) (s : ℝ) :
    (P.flow.metric time).tangentNorm (auxiliaryCircleFiber P x s)
      (curveVelocity (auxiliaryCircleFiber P x) s) = 1 := by
  let := P.circle.chartedSpace
  unfold RiemannianMetric.tangentNorm
  rw [P.metric_eq, auxiliaryCircle_fiber_velocity_split]
  simp only [map_zero, zero_add]
  change Real.sqrt (P.circle.metric.inner (s : AddCircle circumference)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun r : ℝ => (r : AddCircle circumference)) s 1)
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun r : ℝ => (r : AddCircle circumference)) s 1)) = 1
  rw [P.circle.metric_quotient]
  norm_num

theorem auxiliaryCircle_fiber_edist_le
    (P : M62.CircleProductData F circumference) (time : ℝ) (x : M) (s t : ℝ) :
    (P.flow.metric time).edist (x, P.circle.quotient s) (x, P.circle.quotient t) ≤
      ENNReal.ofReal |s - t| := by
  have h := m60Curve_edist_le_of_speed_bound (P.flow.metric time)
    ((auxiliaryCircle_fiber_contMDiff P x).of_le (by simp)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun r => (auxiliaryCircle_fiber_speed P time x r).le) s t
  simpa only [auxiliaryCircleFiber, ENNReal.ofReal_one, one_mul] using h

theorem auxiliaryCircle_product_edist_le
    (P : M62.CircleProductData F circumference) (time : ℝ) (x y : M) (s t : ℝ) :
    (P.flow.metric time).edist (x, P.circle.quotient s) (y, P.circle.quotient t) ≤
      (F.metric time).edist x y + ENNReal.ofReal |s - t| := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨(P.flow.metric time).toRiemannianMetric⟩
  calc
    (P.flow.metric time).edist (x, P.circle.quotient s) (y, P.circle.quotient t) ≤
        (P.flow.metric time).edist (x, P.circle.quotient s) (y, P.circle.quotient s) +
          (P.flow.metric time).edist (y, P.circle.quotient s) (y, P.circle.quotient t) :=
      Manifold.riemannianEDist_triangle
    _ ≤ (F.metric time).edist x y + ENNReal.ofReal |s - t| := by
      rw [auxiliaryCircle_section_edist]
      exact add_le_add le_rfl (auxiliaryCircle_fiber_edist_le P time y s t)

end PoincareConjecture.M64

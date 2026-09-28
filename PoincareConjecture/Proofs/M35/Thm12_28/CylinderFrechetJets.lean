import PoincareConjecture.Proofs.M35.Thm12_28.CylinderJetEstimates
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCharts










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35



theorem iteratedFDeriv_cylinderCoordinateEquiv
    (f : RoundCylinderCoordinates → ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (r : ℕ) (v : Fin r → EuclideanSpace ℝ (Fin 3)) :
    iteratedFDeriv ℝ r (f ∘ cylinderCoordinateEquiv) p v =
      iteratedFDeriv ℝ r f (cylinderCoordinateEquiv p)
        (fun i => cylinderCoordinateEquiv (v i)) := by
  have h := cylinderCoordinateEquiv.iteratedFDerivWithin_comp_right f
    uniqueDiffOn_univ (mem_univ (cylinderCoordinateEquiv p)) r
  have he := congrArg (fun A => A v) h
  simpa only [preimage_univ, iteratedFDerivWithin_univ,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe] using he

private theorem second_derivative_evaluation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {p : V} (hf : ContDiffAt ℝ ∞ f p) (v w : V) :
    (fderiv ℝ (fderiv ℝ f) p w) v =
      fderiv ℝ (fun y => fderiv ℝ f y v) p w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by norm_num)
  have h := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp p hd.hasFDerivAt
  convert! (congrArg (fun L : V →L[ℝ] ℝ => L w) h.fderiv).symm using 1

end PoincareConjecture.M35

namespace PoincareConjecture.RoundCylinderClose



theorem iterated_error_component_abs_lt {epsilon u : ℝ} {B : RoundCylinderTwoTensor}
    (h : RoundCylinderClose epsilon u B) (he : 0 < epsilon)
    (hlo : -1 ≤ u) (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hk : 2 ≤ ⌊epsilon⁻¹⌋₊) {r : ℕ} (hr : r ≤ 2)
    (i j : Fin 3) (a : Fin r → Fin 3) :
    |iteratedFDeriv ℝ r (fun p : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
        roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j)
        (0, s) (fun k => roundCylinderCoordinateBasis (a k))| < 52 * epsilon := by
  have hB := h.contDiffAt_coefficient q (0, s) hs i j
  have hG := (M35.contDiff_roundCylinderGram u q i j).contDiffAt (x := (0, s))
  interval_cases r
  · have hb := h.component_abs_lt he hlo hu (z := (q, s)) hs (Nat.zero_le _) ![i, j]
    dsimp only at hb
    rw [M35.sphere_chart_center] at hb
    norm_num [roundCylinderIteratedDerivative] at hb
    simp only [iteratedFDeriv_zero_apply]
    linarith
  · have hb := h.first_component_abs_lt he hlo hu q s hs (by omega) ![a 0, i, j]
    change |fderiv ℝ (fun p : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j)
      (0, s) (roundCylinderCoordinateBasis (a 0))| < 8 * epsilon at hb
    rw [iteratedFDeriv_one_apply]
    have hd := (hB.differentiableAt (by simp)).hasFDerivAt.sub
      (M35.hasFDerivAt_roundCylinderGram_center u q s i j)
    have hd' : fderiv ℝ (fun p : RoundCylinderCoordinates =>
        roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
          roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j) (0, s) =
        fderiv ℝ (fun p : RoundCylinderCoordinates =>
          roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j)
          (0, s) := by
      convert! hd.fderiv using 1
      simp only [sub_zero]
    have heq := congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
      |L (roundCylinderCoordinateBasis (a 0))|) hd'
    exact heq.trans_lt (hb.trans_le (by linarith))
  · have hb := h.second_error_component_abs_lt he hlo hu q s hs hk ![a 0, a 1, i, j]
    dsimp only at hb
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at hb
    rw [iteratedFDeriv_two_apply, M35.second_derivative_evaluation (hB.sub hG)]
    exact hb

end PoincareConjecture.RoundCylinderClose

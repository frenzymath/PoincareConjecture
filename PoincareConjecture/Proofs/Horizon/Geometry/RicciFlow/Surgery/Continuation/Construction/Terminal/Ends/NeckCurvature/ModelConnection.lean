import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.ModelConnection








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

open Set
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture

private theorem fderiv_cylinderFactor (p v : RoundCylinderCoordinates) :
    fderiv ℝ (fun z : RoundCylinderCoordinates => 32 / (‖z.1‖ ^ 2 + 4) ^ 2) p v =
      -128 * inner ℝ p.1 v.1 / (‖p.1‖ ^ 2 + 4) ^ 3 := by
  have hpos : 0 < ‖p.1‖ ^ 2 + 4 := by positivity
  have houter := (hasDerivAt_const (‖p.1‖ ^ 2) (32 : ℝ)).div
    (((hasDerivAt_id (‖p.1‖ ^ 2)).add_const (4 : ℝ)).pow 2)
      (pow_ne_zero _ hpos.ne')
  have h := houter.comp_hasFDerivAt p
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).hasFDerivAt.norm_sq
  have heq := congrArg (fun L => L v) h.fderiv
  simp only [Function.comp_def, Pi.div_apply, Pi.pow_apply, id_eq, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', innerSL_apply_apply,
    smul_eq_mul] at heq
  rw [heq]
  field_simp
  ring

private theorem fderiv_cylinderGram (q : UnitTwoSphere) (p v : RoundCylinderCoordinates)
    (a b : Fin 3) :
    fderiv ℝ (fun z => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) z a b) p v =
      (-128 * inner ℝ p.1 v.1 / (‖p.1‖ ^ 2 + 4) ^ 3) *
        inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 := by
  have hfactor : DifferentiableAt ℝ
      (fun z : RoundCylinderCoordinates => 32 / (‖z.1‖ ^ 2 + 4) ^ 2) p := by
    have houter : DifferentiableAt ℝ (fun x : ℝ => 32 / (x + 4) ^ 2) (‖p.1‖ ^ 2) := by
      fun_prop (disch := positivity)
    have hinner : DifferentiableAt ℝ (fun z : RoundCylinderCoordinates => ‖z.1‖ ^ 2) p :=
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).differentiableAt.norm_sq
        (𝕜 := ℝ)
    exact houter.comp (f := fun z : RoundCylinderCoordinates => ‖z.1‖ ^ 2)
      (g := fun x : ℝ => 32 / (x + 4) ^ 2) p hinner
  have heq : (fun z => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) z a b) =
      fun z => (32 / (‖z.1‖ ^ 2 + 4) ^ 2) *
        inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 +
        (roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2 := by
    funext z
    rw [roundCylinderGram_eq_stereographic_formula]
    ring
  rw [heq, fderiv_add_const, fderiv_mul_const hfactor, smul_apply,
    fderiv_cylinderFactor]
  simp only [smul_eq_mul]
  ring

theorem fderiv_fderiv_roundCylinderGram_center (q : UnitTwoSphere) (s : ℝ)
    (u v : RoundCylinderCoordinates) (a b : Fin 3) :
    fderiv ℝ (fderiv ℝ (fun p => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)) (0, s) u v =
      -2 * inner ℝ u.1 v.1 *
        inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 := by
  let L : RoundCylinderCoordinates →L[ℝ] ℝ :=
    (innerSL ℝ v.1).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
  have hL (p : RoundCylinderCoordinates) : L p = inner ℝ p.1 v.1 := by
    change inner ℝ v.1 p.1 = _
    exact real_inner_comm _ _
  have hfactor : DifferentiableAt ℝ
      (fun p : RoundCylinderCoordinates => -128 / (‖p.1‖ ^ 2 + 4) ^ 3) (0, s) := by
    have houter : DifferentiableAt ℝ (fun x : ℝ => -128 / (x + 4) ^ 3)
        (‖(0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2) := by
      fun_prop (disch := norm_num)
    have hinner : DifferentiableAt ℝ (fun z : RoundCylinderCoordinates => ‖z.1‖ ^ 2)
        (0, s) :=
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).differentiableAt.norm_sq
        (𝕜 := ℝ)
    exact houter.comp (f := fun z : RoundCylinderCoordinates => ‖z.1‖ ^ 2)
      (g := fun x : ℝ => -128 / (x + 4) ^ 3) (0, s) hinner
  have heq : (fun p => fderiv ℝ (fun z => roundCylinderGram 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) z a b) p v) =
      fun p => ((-128 / (‖p.1‖ ^ 2 + 4) ^ 3) * L p) *
        inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 := by
    funext p
    rw [fderiv_cylinderGram, hL]
    ring
  have hd := (contDiff_roundCylinderGram 0 q a b).contDiffAt (x := (0, s)) |>.fderiv_right
    (m := ∞) (by simp)
  have happly := fderiv_clm_apply (hd.differentiableAt (by simp))
    (differentiableAt_const v)
  have hcomp := congrArg (fun f : RoundCylinderCoordinates → ℝ => fderiv ℝ f (0, s) u) heq
  rw [happly] at hcomp
  rw [((hfactor.hasFDerivAt.fun_mul L.hasFDerivAt).mul_const
    (inner ℝ (roundCylinderCoordinateBasis a).1
      (roundCylinderCoordinateBasis b).1)).fderiv] at hcomp
  simp only [ContinuousLinearMap.flip_apply, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add, add_apply, smul_apply, smul_eq_mul,
    hL, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add, inner_zero_left,
    zero_smul, zero_mul, zero_apply, add_zero] at hcomp
  norm_num at hcomp
  rw [hcomp]
  ring

theorem roundCylinderChristoffel_eq_explicit (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (a b d : Fin 3) :
    roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d =
      (-2 / (‖p.1‖ ^ 2 + 4)) *
        (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis d).1 *
            inner ℝ p.1 (roundCylinderCoordinateBasis b).1 +
          inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 *
            inner ℝ p.1 (roundCylinderCoordinateBasis d).1 -
          inner ℝ (roundCylinderCoordinateBasis b).1 (roundCylinderCoordinateBasis d).1 *
            inner ℝ p.1 (roundCylinderCoordinateBasis a).1) := by
  have hpos : 0 < ‖p.1‖ ^ 2 + 4 := by positivity
  have hGram : roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p =
      Matrix.diagonal (fun i : Fin 3 => if i = 2 then 1 else
        32 / (‖p.1‖ ^ 2 + 4) ^ 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [roundCylinderGram_eq_stereographic_formula, Matrix.diagonal,
        roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_left, PiLp.single_apply, Fin.ext_iff] <;> ring
  have hinv : (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)⁻¹ =
      Matrix.diagonal (fun i : Fin 3 => if i = 2 then 1 else
        (‖p.1‖ ^ 2 + 4) ^ 2 / 32) := by
    apply Matrix.inv_eq_left_inv
    rw [hGram, Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.diagonal, Fin.ext_iff] <;> field_simp
  simp only [roundCylinderChristoffel, hinv, fderiv_cylinderGram]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    norm_num [Fin.ext_iff,
      roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply] <;>
    field_simp <;> ring

theorem fderiv_roundCylinderChristoffel_center_explicit
    (q : UnitTwoSphere) (s : ℝ) (a b d i : Fin 3) :
    fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s)
      (roundCylinderCoordinateBasis i) =
      (-1 / 2 : ℝ) *
        (inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis d).1 *
            inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis b).1 +
          inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 *
            inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis d).1 -
          inner ℝ (roundCylinderCoordinateBasis b).1 (roundCylinderCoordinateBasis d).1 *
            inner ℝ (roundCylinderCoordinateBasis i).1 (roundCylinderCoordinateBasis a).1) := by
  let L (j : Fin 3) : RoundCylinderCoordinates →L[ℝ] ℝ :=
    (innerSL ℝ (roundCylinderCoordinateBasis j).1).comp
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ)
  have hL (j : Fin 3) (p : RoundCylinderCoordinates) :
      L j p = inner ℝ p.1 (roundCylinderCoordinateBasis j).1 := by
    change inner ℝ (roundCylinderCoordinateBasis j).1 p.1 = _
    exact real_inner_comm _ _
  let V :=
    inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis d).1 • L b +
      inner ℝ (roundCylinderCoordinateBasis a).1 (roundCylinderCoordinateBasis b).1 • L d -
      inner ℝ (roundCylinderCoordinateBasis b).1 (roundCylinderCoordinateBasis d).1 • L a
  have hfactor : DifferentiableAt ℝ
      (fun p : RoundCylinderCoordinates => -2 / (‖p.1‖ ^ 2 + 4)) (0, s) := by
    have houter : DifferentiableAt ℝ (fun x : ℝ => -2 / (x + 4))
        (‖(0 : EuclideanSpace ℝ (Fin 2))‖ ^ 2) := by
      fun_prop (disch := norm_num)
    have hinner : DifferentiableAt ℝ (fun z : RoundCylinderCoordinates => ‖z.1‖ ^ 2)
        (0, s) :=
      (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).differentiableAt.norm_sq
        (𝕜 := ℝ)
    exact houter.comp (f := fun z : RoundCylinderCoordinates => ‖z.1‖ ^ 2)
      (g := fun x : ℝ => -2 / (x + 4)) (0, s) hinner
  have heq : (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) =
      fun p => (-2 / (‖p.1‖ ^ 2 + 4)) * V p := by
    funext p
    rw [roundCylinderChristoffel_eq_explicit]
    simp only [V, sub_apply, add_apply, smul_apply, smul_eq_mul, hL]
  rw [heq]
  have hd := (hfactor.hasFDerivAt.fun_mul V.hasFDerivAt).fderiv
  rw [hd]
  simp only [add_apply, smul_apply, smul_eq_mul,
    V, hL, sub_apply, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    zero_add, inner_zero_left, mul_zero, add_zero, sub_zero, zero_mul]
  norm_num

theorem abs_fderiv_roundCylinderChristoffel_center_le_half
    (q : UnitTwoSphere) (s : ℝ) (a b d i : Fin 3) :
    |fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s)
      (roundCylinderCoordinateBasis i)| ≤ 1 / 2 := by
  rw [fderiv_roundCylinderChristoffel_center_explicit]
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases i <;>
    norm_num [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply]

theorem sum_abs_fderiv_roundCylinderChristoffel_center_le_half
    (q : UnitTwoSphere) (s : ℝ) (b d i : Fin 3) :
    (∑ a : Fin 3, |fderiv ℝ (fun p => roundCylinderChristoffel 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b d) (0, s)
      (roundCylinderCoordinateBasis i)|) ≤ 1 / 2 := by
  simp only [fderiv_roundCylinderChristoffel_center_explicit]
  fin_cases b <;> fin_cases d <;> fin_cases i <;>
    norm_num [Fin.sum_univ_succ, roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply]

end PoincareConjecture

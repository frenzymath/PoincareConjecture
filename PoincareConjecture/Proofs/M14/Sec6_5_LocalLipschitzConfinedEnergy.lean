import PoincareConjecture.Proofs.M14.Mathlib.NonnegativeEnergyBound
import PoincareConjecture.Proofs.M14.Sec6_5_SquareScalarEnergy
import PoincareConjecture.Proofs.M14.Sec6_1_SquareRootAction

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem horizontalScalar_abs_le_of_ricci_bound (q : G.Point) {C : ℝ}
    (hRic : ∀ v w : G.Horizontal q, |horizontalRicci G.leafwise q v w| ≤
      C * Real.sqrt (G.spacetime.horizontalMetric.inner q v v) *
        Real.sqrt (G.spacetime.horizontalMetric.inner q w w)) :
    |horizontalScalarCurvature G.leafwise q| ≤ (n : ℝ) * C := by
  let S := G.slices (G.spacetime.timeFunction q)
  let qs : S.Point := spacetimeSlicePoint G.slices q
  let D := G.leafwise.sliceConnection (G.spacetime.timeFunction q)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : S.Point → Type _) :=
    ⟨S.metricOnPoints.toRiemannianMetric⟩
  let b := S.metricOnPoints.orthonormalBasis qs
  have hnorm (i) : G.spacetime.horizontalMetric.inner q
      (S.tangentEquiv qs (b i)) (S.tangentEquiv qs (b i)) = 1 := by
    change G.spacetime.horizontalMetric.inner qs.val
      (S.tangentEquiv qs (b i)) (S.tangentEquiv qs (b i)) = 1
    rw [← S.metric_eq qs]
    exact b.inner_eq_one i
  have hbound (i) : |D.ricci qs (b i) (b i)| ≤ C := by
    have h := hRic (S.tangentEquiv qs (b i)) (S.tangentEquiv qs (b i))
    simpa only [horizontalRicci, S, qs, D, ContinuousLinearEquiv.symm_apply_apply,
      hnorm, Real.sqrt_one, mul_one] using h
  change |∑ i, D.ricci qs (b i) (b i)| ≤ _
  calc
    _ ≤ ∑ i, |D.ricci qs (b i) (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) qs)), C :=
      Finset.sum_le_sum (fun i _ => hbound i)
    _ = _ := by
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) qs) = n := by
        change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
        simp
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hdim, nsmul_eq_mul]

variable {T b : ℝ} {x y : G.Point} {p : M14BackwardPath G T 0 b x y}

theorem squareRoot_energy_action_bound
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 b)
      R.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval 0 b, ∀ W,
      M14SquareRootEulerResidual G R E s W = 0)
    {H CR Cgrad : ℝ} (hH : Real.sqrt b ≤ H) (hCR : 0 ≤ CR) (hCgrad : 0 ≤ Cgrad)
    (hRic : ∀ s ∈ M14SqrtParameterInterval 0 b, ∀ v w : G.Horizontal (R.curve s),
      |horizontalRicci G.leafwise (R.curve s) v w| ≤
        CR * Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s) v v) *
          Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s) w w))
    (hgrad : ∀ s ∈ M14SqrtParameterInterval 0 b, ∀ v : G.Horizontal (R.curve s),
      |M14HorizontalScalarDifferential G (R.curve s) v.val| ≤
        Cgrad * Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s) v v))
    {r : ℝ} (hr : r ∈ M14SqrtParameterInterval 0 b) :
    Real.sqrt b * (G.spacetime.horizontalMetric.inner (R.curve r)
      (R.horizontal_velocity r) (R.horizontal_velocity r) + 1) ≤
      Real.exp ((2 * H ^ 2 * Cgrad + 4 * H * CR) * Real.sqrt b) *
        (2 * M14BackwardLAction G p + 4 * ((n : ℝ) * CR) * (Real.sqrt b) ^ 3 +
          Real.sqrt b) := by
  let e : ℝ → ℝ := fun s => G.spacetime.horizontalMetric.inner (R.curve s)
    (R.horizontal_velocity s) (R.horizontal_velocity s)
  let d : ℝ → ℝ := fun s => 4 * s ^ 2 *
    M14HorizontalScalarDifferential G (R.curve s) (R.horizontal_velocity s).val -
      4 * s * horizontalRicci G.leafwise (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s)
  let A := 2 * H ^ 2 * Cgrad + 4 * H * CR
  have hH0 : 0 ≤ H := (Real.sqrt_nonneg b).trans hH
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : M14SqrtParameterInterval 0 b = Icc 0 (Real.sqrt b) := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero]
  have he (s : ℝ) : 0 ≤ e s := by
    exact (G.spacetime.horizontalMetric.toRiemannianMetric.toCore (R.curve s)).re_inner_nonneg _
  have hc : ContinuousOn e (Icc 0 (Real.sqrt b)) := by
    simpa only [← hC] using (squareRoot_energy_contDiffOn R).continuousOn
  have hd (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt b)) :
      HasDerivWithinAt e (d s) (Icc 0 (Real.sqrt b)) s := by
    simpa only [hC, e, d] using squareRoot_energy_hasDerivWithinAt R E
      (hC.symm ▸ hs) (hEuler s (hC.symm ▸ hs))
  have hbound (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt b)) : |d s| ≤ A * (e s + 1) := by
    have hRic' := hRic s (hC.symm ▸ hs) (R.horizontal_velocity s) (R.horizontal_velocity s)
    have hRic'' : |horizontalRicci G.leafwise (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s)| ≤ CR * e s := by
      change |horizontalRicci G.leafwise (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s)| ≤
          CR * Real.sqrt (e s) * Real.sqrt (e s) at hRic'
      rwa [mul_assoc, Real.mul_self_sqrt (he s)] at hRic'
    exact Proofs.M09.regularizedEnergy_abs_bound s H CR Cgrad (e s) _ _ hs.1
      (hs.2.trans hH) hCR hCgrad (he s) (hgrad s (hC.symm ▸ hs) _) hRic''
  have hRc : ContinuousOn (fun s => horizontalScalarCurvature G.leafwise (R.curve s))
      (Icc 0 (Real.sqrt b)) := by
    simpa only [← hC] using (squareRoot_scalar_contDiffOn hM12 R).continuousOn
  have hR (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt b)) :
      -((n : ℝ) * CR) ≤ horizontalScalarCurvature G.leafwise (R.curve s) :=
    (abs_le.mp (horizontalScalar_abs_le_of_ricci_bound (R.curve s)
      (hRic s (hC.symm ▸ hs)))).1
  have h := nonnegativeEnergy_action_bound_within e d
    (fun s => horizontalScalarCurvature G.leafwise (R.curve s)) (Real.sqrt_nonneg b)
    hA (mul_nonneg (Nat.cast_nonneg n) hCR) hc (fun s _ => he s) hd hbound hRc hR
    (hC ▸ hr)
  have haction : (∫ s in (0 : ℝ)..Real.sqrt b,
      2 * s ^ 2 * horizontalScalarCurvature G.leafwise (R.curve s) + (1 / 2 : ℝ) * e s) =
      M14BackwardLAction G p := by
    simpa only [Real.sqrt_zero, squareRootLIntegrand, e] using
      integral_squareRootLIntegrand_eq_action R
  rwa [haction] at h

theorem squareRoot_energy_uniform_bound
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 b)
      R.horizontal_velocity)
    (hEuler : ∀ s ∈ M14SqrtParameterInterval 0 b, ∀ W,
      M14SquareRootEulerResidual G R E s W = 0)
    {δ H CR Cgrad D : ℝ} (hδ : 0 < δ) (hδb : δ ≤ Real.sqrt b)
    (hH : Real.sqrt b ≤ H) (hCR : 0 ≤ CR) (hCgrad : 0 ≤ Cgrad) (hD : 0 ≤ D)
    (hL : M14BackwardLAction G p ≤ D)
    (hRic : ∀ s ∈ M14SqrtParameterInterval 0 b, ∀ v w : G.Horizontal (R.curve s),
      |horizontalRicci G.leafwise (R.curve s) v w| ≤
        CR * Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s) v v) *
          Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s) w w))
    (hgrad : ∀ s ∈ M14SqrtParameterInterval 0 b, ∀ v : G.Horizontal (R.curve s),
      |M14HorizontalScalarDifferential G (R.curve s) v.val| ≤
        Cgrad * Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s) v v))
    {r : ℝ} (hr : r ∈ M14SqrtParameterInterval 0 b) :
    let A := 2 * H ^ 2 * Cgrad + 4 * H * CR
    let B := Real.exp (A * H) * (2 * D + 4 * ((n : ℝ) * CR) * H ^ 3 + H)
    G.spacetime.horizontalMetric.inner (R.curve r)
      (R.horizontal_velocity r) (R.horizontal_velocity r) + 4 * r ^ 2 ≤
      (Real.sqrt (B / δ + 4 * H ^ 2)) ^ 2 := by
  let e := G.spacetime.horizontalMetric.inner (R.curve r)
    (R.horizontal_velocity r) (R.horizontal_velocity r)
  let A := 2 * H ^ 2 * Cgrad + 4 * H * CR
  let C := (n : ℝ) * CR
  let B := Real.exp (A * H) * (2 * D + 4 * C * H ^ 3 + H)
  change e + 4 * r ^ 2 ≤ (Real.sqrt (B / δ + 4 * H ^ 2)) ^ 2
  have hH0 : 0 ≤ H := (Real.sqrt_nonneg b).trans hH
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg n) hCR
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he : 0 ≤ e :=
    (G.spacetime.horizontalMetric.toRiemannianMetric.toCore (R.curve r)).re_inner_nonneg _
  have hcontrol := squareRoot_energy_action_bound hM12 R E hEuler hH hCR hCgrad hRic hgrad hr
  have hterm : 2 * M14BackwardLAction G p + 4 * C * (Real.sqrt b) ^ 3 + Real.sqrt b ≤
      2 * D + 4 * C * H ^ 3 + H := by
    gcongr
  have hbound : Real.sqrt b * (e + 1) ≤ B := by
    apply hcontrol.trans
    calc
      _ ≤ Real.exp (A * Real.sqrt b) * (2 * D + 4 * C * H ^ 3 + H) :=
        mul_le_mul_of_nonneg_left hterm (Real.exp_nonneg _)
      _ ≤ B := by
        apply mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hH hA))
        positivity
  have heB : e ≤ B / δ := by
    rw [le_div_iff₀ hδ]
    have h := (mul_le_mul_of_nonneg_right hδb (by linarith : 0 ≤ e + 1)).trans hbound
    nlinarith
  have hr0 : 0 ≤ r := by simpa only [Real.sqrt_zero] using hr.1
  have hrH : r ≤ H := hr.2.trans hH
  rw [Real.sq_sqrt (by positivity : 0 ≤ B / δ + 4 * H ^ 2)]
  nlinarith [sq_le_sq₀ hr0 hH0 |>.mpr hrH]

end PoincareConjecture.M14

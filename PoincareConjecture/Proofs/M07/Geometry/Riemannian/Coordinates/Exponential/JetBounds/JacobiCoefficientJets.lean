import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CoframeJacobi
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.ConnectionComponentJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.OperatorComponentJets












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Topology BigOperators Manifold

namespace PoincareConjecture.CoordinateExponential

open Poincare.Riemannian.RadialTransport

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


def radialJacobiCoefficientJetBound (n m : ℕ) (r : ℝ) (C : ℕ → ℝ) : ℝ :=
  n * n * (n * n * scalarJetProductBound m
    (fun j => scalarJetProductBound j C (fun _ => max 1 r)) (fun _ => max 1 r))

theorem radialJacobiCoefficientJetBound_nonneg (n m : ℕ) (r : ℝ) (C : ℕ → ℝ) :
    0 ≤ radialJacobiCoefficientJetBound n m r C := by
  unfold radialJacobiCoefficientJetBound
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (scalarJetProductBound_nonneg ..))



theorem norm_iteratedFDeriv_radialJacobiCoefficient_le
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    (hgeo : ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
      christoffelBilinear g.euclideanCoefficients (t • x) x x = 0)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (m : ℕ) (C : ℕ → ℝ) {r : ℝ}
    (hC : ∀ q ≤ m, ∀ J : Fin 4 → Fin n, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      ‖iteratedFDeriv ℝ q (radialCurvatureComponent D 0 (fun i => b (J i))) x‖ ≤ C q)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 r) :
    ‖iteratedFDeriv ℝ m
      (fun y => radialJacobiCoefficient (christoffelBilinear g.euclideanCoefficients) T (t, y)) x‖ ≤
      radialJacobiCoefficientJetBound n m r C := by
  classical
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
      (g.inner_isInvertible y)
  have htx : t • x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    have hnorm : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)).trans_eq (one_mul _)
    simpa only [mem_ball, dist_zero_right] using hnorm.trans_lt (by simpa using hx)
  let K := scalarJetProductBound m
    (fun j => scalarJetProductBound j C (fun _ => max 1 r)) (fun _ => max 1 r)
  apply norm_iteratedFDeriv_operator_le_of_components b
    ((contDiff_radialJacobiCoefficient hΓ hT hTi).comp (contDiff_const.prodMk contDiff_id))
    m
  intro j a
  have he : (fun y => inner ℝ (b a) (radialJacobiCoefficient Γ T (t, y) (b j))) =
      fun y => ∑ i, ∑ k, b.repr y i * (b.repr y k *
        radialCurvatureComponent D 0 ![b j, b i, b a, b k] (t • y)) := by
    funext y
    rw [real_inner_comm, radialJacobiCoefficient_eq_kernel hΓ hgeo hTv,
      inner_radialCurvatureKernel_eq_component D h0 hTi hTv,
      radialCurvatureComponent_four_eq_sum_velocity D b hTv]
  simp only [Function.comp_def, id_eq]
  rw [he]
  let L : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun i => innerSL ℝ (b i)
  let c (i k : Fin n) (y : EuclideanSpace ℝ (Fin n)) :=
    radialCurvatureComponent D 0 ![b j, b i, b a, b k] (t • y)
  have hc (i k) : ContDiff ℝ ∞ (c i k) :=
    (contDiff_radialCurvatureComponent D 0 _).comp (contDiff_id.const_smul t)
  have hcb (i k) (q : ℕ) (hq : q ≤ m) : ‖iteratedFDeriv ℝ q (c i k) x‖ ≤ C q := by
    have hv : (fun l => b (![j, i, a, k] l)) = ![b j, b i, b a, b k] := by
      ext l
      fin_cases l <;> rfl
    have hh := hC q hq ![j, i, a, k] (t • x) htx
    rw [hv] at hh
    dsimp only [c]
    rw [iteratedFDeriv_comp_const_smul t
      ((contDiff_radialCurvatureComponent D 0 _).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl q))]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht.1 q)]
    exact ((mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1 ht.2) (norm_nonneg _)).trans_eq
      (one_mul _)).trans hh
  have hL (i) : ‖L i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [L, innerSL_apply_apply, b.norm_eq_one, one_mul] using norm_inner_le_norm (b i) v
  have hx' : ‖x‖ ≤ r := by simpa using (mem_ball.mp hx).le
  have hinner (i k) (q : ℕ) (hq : q ≤ m) :
      ‖iteratedFDeriv ℝ q (fun y => L k y * c i k y) x‖ ≤
        scalarJetProductBound q C (fun _ => max 1 r) := by
    simpa only [mul_one] using norm_iteratedFDeriv_position_mul_le_scaled_bound
      (L k) (hL k) (hc i k) q C hx' (s := 1) zero_le_one
      (fun v hv => by simpa only [mul_one] using hcb i k v (hv.trans hq))
  have hterm (i k) : ‖iteratedFDeriv ℝ m (fun y => L i y * (L k y * c i k y)) x‖ ≤ K := by
    simpa only [mul_one] using norm_iteratedFDeriv_position_mul_le_scaled_bound
      (L i) (hL i) ((L k).contDiff.mul (hc i k)) m
      (fun q => scalarJetProductBound q C (fun _ => max 1 r)) hx' (s := 1) zero_le_one
      (fun q hq => by simpa only [mul_one] using hinner i k q hq)
  have hm : (m : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  have hs (i) := norm_iteratedFDeriv_sum_le_const
    (fun k => (((L i).contDiff.mul ((L k).contDiff.mul (hc i k))).of_le hm).contDiffAt)
    (hterm i)
  have hall := norm_iteratedFDeriv_sum_le_const
    (fun i => ContDiffAt.sum (fun k _ =>
      (((L i).contDiff.mul ((L k).contDiff.mul (hc i k))).of_le hm).contDiffAt)) hs
  simpa only [Fintype.card_fin, mul_assoc, L, c, OrthonormalBasis.repr_apply_apply,
    innerSL_apply_apply] using hall

end PoincareConjecture.CoordinateExponential

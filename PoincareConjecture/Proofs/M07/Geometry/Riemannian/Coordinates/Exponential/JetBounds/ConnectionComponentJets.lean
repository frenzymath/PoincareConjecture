import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FrameJetBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.RadialIntegral
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureComponentExpansion












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Topology BigOperators

namespace PoincareConjecture.CoordinateExponential

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem norm_iteratedFDeriv_linear_coordinate_le
    (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (m : ℕ) {x : E} {r : ℝ}
    (hx : ‖x‖ ≤ r) : ‖iteratedFDeriv ℝ m L x‖ ≤ max 1 r := by
  cases m with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    exact (L.le_opNorm x).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg x)).trans
      (by simpa only [one_mul] using hx.trans (le_max_right 1 r)))
  | succ m =>
    rw [← norm_iteratedFDeriv_fderiv]
    have he : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
    rw [he]
    cases m with
    | zero => simpa only [norm_iteratedFDeriv_zero] using hL.trans (le_max_left 1 r)
    | succ m => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; positivity

theorem norm_iteratedFDeriv_position_mul_le_scaled_bound
    (L : E →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (A : ℕ → ℝ)
    {x : E} {r s : ℝ} (hx : ‖x‖ ≤ r) (hs : 0 ≤ s)
    (hA : ∀ j ≤ m, ‖iteratedFDeriv ℝ j f x‖ ≤ A j * s) :
    ‖iteratedFDeriv ℝ m (fun y => L y * f y) x‖ ≤
      scalarJetProductBound m A (fun _ => max 1 r) * s := by
  have hm : (m : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  simpa only [mul_comm] using norm_iteratedFDeriv_mul_le_scaled_bound isOpen_univ
    (hf.of_le hm).contDiffOn (L.contDiff.of_le hm).contDiffOn (mem_univ x)
    A (fun _ => max 1 r) hs hA (fun j _ => norm_iteratedFDeriv_linear_coordinate_le L hL j hx)


def connectionComponentJetBound (n m : ℕ) (r : ℝ) (A C : ℕ → ℝ) : ℝ :=
  n * n * scalarJetProductBound m
    (fun j => scalarJetProductBound j A C) (fun _ => max 1 r) / (m + 1)

theorem connectionComponentJetBound_nonneg (n m : ℕ) (r : ℝ) (A C : ℕ → ℝ) :
    0 ≤ connectionComponentJetBound n m r A C := by
  exact div_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (scalarJetProductBound_nonneg ..)) (by positivity)

variable [FiniteDimensional ℝ E]



theorem norm_iteratedFDeriv_radial_component_integral_le
    {n : ℕ} (L : Fin n → E →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    {a : Fin n → E → ℝ} {c : Fin n → Fin n → E → ℝ}
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (hc : ∀ i j, ContDiff ℝ ∞ (c i j))
    (m : ℕ) (A C : ℕ → ℝ) {r s : ℝ} (hs : 0 ≤ s)
    (hA : ∀ j ≤ m, ∀ i, ∀ x ∈ ball (0 : E) r,
      ‖iteratedFDeriv ℝ j (a i) x‖ ≤ A j * s)
    (hC : ∀ j ≤ m, ∀ i k, ∀ x ∈ ball (0 : E) r,
      ‖iteratedFDeriv ℝ j (c i k) x‖ ≤ C j)
    {x : E} (hx : x ∈ ball (0 : E) r) :
    ‖iteratedFDeriv ℝ m
      (radialWeightedIntegral 0 (fun y => ∑ i, ∑ k, L i y * (a k y * c i k y))) x‖ ≤
      connectionComponentJetBound n m r A C * s := by
  classical
  have hr : 0 ≤ r := (norm_nonneg x).trans (by simpa using (mem_ball.mp hx).le)
  let B := fun j => scalarJetProductBound j A C
  let K := scalarJetProductBound m B (fun _ => max 1 r)
  have hK : 0 ≤ K := scalarJetProductBound_nonneg ..
  have hsum : ContDiff ℝ ∞ (fun y => ∑ i, ∑ k, L i y * (a k y * c i k y)) :=
    ContDiff.sum (fun i _ => ContDiff.sum (fun k _ => (L i).contDiff.mul ((ha k).mul (hc i k))))
  have hb (y : E) (hy : y ∈ ball (0 : E) r) :
      ‖iteratedFDeriv ℝ m (fun y => ∑ i, ∑ k, L i y * (a k y * c i k y)) y‖ ≤
        n * n * K * s := by
    have hm : (m : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
    have hprod (i k) (j : ℕ) (hj : j ≤ m) :
        ‖iteratedFDeriv ℝ j (fun y => a k y * c i k y) y‖ ≤ B j * s :=
      norm_iteratedFDeriv_mul_le_scaled_bound isOpen_univ
        ((ha k).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffOn
        ((hc i k).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j)).contDiffOn
        (mem_univ y) A C hs
        (fun q hq => hA q (hq.trans hj) k y hy)
        (fun q hq => hC q (hq.trans hj) i k y hy)
    have hterm (i k) : ‖iteratedFDeriv ℝ m (fun y => L i y * (a k y * c i k y)) y‖ ≤ K * s :=
      norm_iteratedFDeriv_position_mul_le_scaled_bound (L i) (hL i)
        ((ha k).mul (hc i k)) m B (by simpa using (mem_ball.mp hy).le) hs (hprod i k)
    have hinner (i) := norm_iteratedFDeriv_sum_le_const
      (fun k => (((L i).contDiff.mul ((ha k).mul (hc i k))).of_le hm).contDiffAt) (hterm i)
    have houter := norm_iteratedFDeriv_sum_le_const
      (fun i => ContDiffAt.sum (fun k _ =>
        (((L i).contDiff.mul ((ha k).mul (hc i k))).of_le hm).contDiffAt)) hinner
    simpa only [Fintype.card_fin, mul_assoc] using houter
  have h := norm_iteratedFDeriv_radialWeightedIntegral_le m 0 hsum.contDiffOn hx
    (show 0 ≤ (n : ℝ) * n * K * s by positivity) (fun t ht => hb (t • x) ?_)
  · simpa only [connectionComponentJetBound, K, B, Nat.cast_zero, zero_add,
      div_mul_eq_mul_div] using h
  · have htx : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)).trans_eq (one_mul _)
    simpa only [mem_ball, dist_zero_right] using htx.trans_lt (by simpa using hx)

section Metric

open Poincare.Riemannian.RadialTransport
open scoped Manifold

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



theorem radialConnectionCoeff_eq_component_integral
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    (hgeo : ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
      christoffelBilinear g.euclideanCoefficients (t • x) x x = 0)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (j a : Fin n) (x u : EuclideanSpace ℝ (Fin n)) :
    radialConnectionCoeff b (christoffelBilinear g.euclideanCoefficients) T j a x u =
      radialWeightedIntegral 0 (fun y => ∑ i, ∑ k, b.repr y i *
        (radialCoframeCoeff b T k y u *
          radialCurvatureComponent D 0 ![b i, b k, b a, b j] y)) x := by
  classical
  let Γ := christoffelBilinear g.euclideanCoefficients
  have hΓ : ContDiff ℝ ∞ Γ := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => contDiffAt_christoffelBilinear (g.contDiffAt_euclideanCoefficients y)
      (g.inner_isInvertible y)
  have hInv : ContDiff ℝ ∞ (fun y => (T y).inverse) := by
    rw [contDiff_iff_contDiffAt]
    exact fun y => (hTi y).contDiffAt_map_inverse.comp y hT.contDiffAt
  let F : ℝ → EuclideanSpace ℝ (Fin n) := fun t =>
    radialCurvatureKernel Γ T (t • x) x ((T (t • x)).inverse (t • u)) (b j)
  have hF : Continuous F := by
    have hq : ContDiff ℝ ∞ (fun t : ℝ => t • x) := contDiff_id.smul contDiff_const
    exact (((contDiff_radialCurvatureKernel hΓ hT hTi).comp
      (hq.prodMk (contDiff_const.prodMk
        ((hInv.comp hq).clm_apply (contDiff_id.smul contDiff_const))))).clm_apply
          contDiff_const).continuous
  rw [radialConnectionCoeff, radialFrameConnection_eq_integral_kernel hΓ hgeo hT hTi hTv]
  change b.repr (∫ t : ℝ in 0..1, F t) a = _
  rw [OrthonormalBasis.repr_apply_apply]
  change (innerSL ℝ (b a)) (∫ t : ℝ in 0..1, F t) = _
  rw [← (innerSL ℝ (b a)).intervalIntegral_comp_comm (hF.intervalIntegrable 0 1)]
  unfold radialWeightedIntegral
  apply intervalIntegral.integral_congr
  intro t _
  simp only [pow_zero, one_smul, innerSL_apply_apply]
  rw [real_inner_comm]
  change inner ℝ (radialCurvatureKernel Γ T (t • x) x
    ((T (t • x)).inverse (t • u)) (b j)) (b a) = _
  rw [inner_radialCurvatureKernel_eq_component D h0 hTi hTv,
    radialCurvatureComponent_four_eq_sum_two D b hTv]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [radialCoframeCoeff, map_smul, PiLp.smul_apply, smul_eq_mul]
  ring



theorem norm_iteratedFDeriv_radialConnectionCoeff_le
    (D : LeviCivitaData g)
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (h0 : ∀ v w : EuclideanSpace ℝ (Fin n), g.inner 0 v w = inner ℝ v w)
    (hgeo : ∀ x : EuclideanSpace ℝ (Fin n), ∀ t : ℝ,
      christoffelBilinear g.euclideanCoefficients (t • x) x x = 0)
    {T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)}
    (hT : ContDiff ℝ ∞ T) (hTi : ∀ x, (T x).IsInvertible)
    (hTv : ∀ x v, T x v = field (christoffelBilinear g.euclideanCoefficients) v x)
    (m : ℕ) (A C : ℕ → ℝ) {r : ℝ}
    (hA : ∀ q ≤ m, ∀ a u, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      ‖iteratedFDeriv ℝ q (fun y => radialCoframeCoeff b T a y u) x‖ ≤ A q * ‖u‖)
    (hC : ∀ q ≤ m, ∀ J : Fin 4 → Fin n, ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r,
      ‖iteratedFDeriv ℝ q (radialCurvatureComponent D 0 (fun i => b (J i))) x‖ ≤ C q)
    (j a : Fin n) (u : EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball 0 r) :
    ‖iteratedFDeriv ℝ m (fun y => radialConnectionCoeff b
      (christoffelBilinear g.euclideanCoefficients) T j a y u) x‖ ≤
      connectionComponentJetBound n m r A C * ‖u‖ := by
  classical
  have he := funext (fun y => radialConnectionCoeff_eq_component_integral
    D b h0 hgeo hT hTi hTv j a y u)
  rw [he]
  let L : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun i => innerSL ℝ (b i)
  have hL (i) : ‖L i‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    simpa only [L, innerSL_apply_apply, b.norm_eq_one, one_mul] using
      norm_inner_le_norm (b i) v
  have h := norm_iteratedFDeriv_radial_component_integral_le L hL
    (fun i => contDiff_radialCoframeCoeff b hT hTi i u)
    (fun i k => contDiff_radialCurvatureComponent D 0 ![b i, b k, b a, b j])
    m A C (norm_nonneg u) (fun q hq i y hy => hA q hq i u y hy)
    (fun q hq i k y hy => ?_) hx
  · simpa only [L, innerSL_apply_apply, OrthonormalBasis.repr_apply_apply] using h
  · have hv : (fun l => b (![i, k, a, j] l)) = ![b i, b k, b a, b j] := by
      ext l
      fin_cases l <;> rfl
    simpa only [hv] using hC q hq ![i, k, a, j] y hy

end Metric

end PoincareConjecture.CoordinateExponential

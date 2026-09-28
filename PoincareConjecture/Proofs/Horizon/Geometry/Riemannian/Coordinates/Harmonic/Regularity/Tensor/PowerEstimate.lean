import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Powers
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Tensor.Cauchy

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators InnerProductSpace

universe u

namespace PoincareConjecture.LeviCivitaData

private theorem tensor_power_absorption {p : ℝ} (hp : 1 ≤ p)
    (h w e y z a : ℝ) :
    2 * h * w * e * y + a * (2 * h * w * e + (2 * p - 2) * h ^ 2 * z + h ^ 2 * y) ≤
      h ^ 2 * y ^ 2 / 2 + (p - 1) * h ^ 2 * z ^ 2 +
        5 * w ^ 2 * e ^ 2 + (p + 1) * h ^ 2 * a ^ 2 := by
  nlinarith only [sq_nonneg (h * y / 2 - 2 * w * e),
    sq_nonneg (h * y / 2 - h * a), sq_nonneg (w * e - h * a),
    mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg (h * (z - a)))]

private theorem tensor_power_weight_sq {w : ℝ} (hw : 0 < w) (p : ℝ) :
    w ^ (2 * p - 2) * w ^ 2 = (w ^ p) ^ 2 := by
  rw [← Real.rpow_mul_natCast hw.le p 2, ← Real.rpow_two, ← Real.rpow_add hw]
  congr 1
  ring

private theorem tensor_power_abs_inner_le_sqrt {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    |inner ℝ u v| ≤ Real.sqrt (inner ℝ u u) * Real.sqrt (inner ℝ v v) := by
  rw [← norm_eq_sqrt_real_inner, ← norm_eq_sqrt_real_inner]
  exact abs_real_inner_le_norm u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem tensor_power_metric_nonneg (x : M) (v : TangentSpace (𝓡 n) x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos x v hv).le

theorem regularized_tensor_power_test_lower (D : LeviCivitaData g)
    {T : CovariantTensorEvaluation n M 2} (hT : IsSmoothCovariantTensor T)
    (F : CovariantTensorEvaluation n M 3)
    {η : M → ℝ} (hη : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η)
    {ε p : ℝ} (hε : 0 < ε) (hp : 1 ≤ p) (x : M) :
    let w := fun y => Real.sqrt (g.tensorPairingTwo T T y + ε)
    let Z : CovariantTensorEvaluation n M 2 :=
      fun y v => (η y ^ 2 * w y ^ (2 * p - 2)) * T y v
    (p - 1 / 2) * (η x ^ 2 * w x ^ (2 * p - 2) *
      g.inner x (D.gradient w x) (D.gradient w x)) ≤
      g.tensorPairingThree (D.covariantTensorDerivative T) (D.covariantTensorDerivative Z) x -
      g.tensorPairingThree F (D.covariantTensorDerivative Z) x +
      5 * ((w x ^ p) ^ 2 * g.inner x (D.gradient η x) (D.gradient η x)) +
      (p + 1) * (η x ^ 2 * w x ^ (2 * p - 2) * g.tensorPairingThree F F x) := by
  let w := fun y => Real.sqrt (g.tensorPairingTwo T T y + ε)
  let Z : CovariantTensorEvaluation n M 2 :=
    fun y v => (η y ^ 2 * w y ^ (2 * p - 2)) * T y v
  let b := g.orthonormalBasis x
  let A := g.tensorPairingThree (D.covariantTensorDerivative T) (D.covariantTensorDerivative T) x
  let B := g.tensorPairingThree F F x
  let W := g.inner x (D.gradient w x) (D.gradient w x)
  let E := g.inner x (D.gradient η x) (D.gradient η x)
  let y := Real.sqrt A
  let a := Real.sqrt B
  let z := Real.sqrt W
  let e := Real.sqrt E
  let s := w x ^ (2 * p - 2)
  let t := w x ^ (2 * p - 3)
  let C := g.tensorPairingThree F (D.covariantTensorDerivative T) x
  let Tη := ∑ i, mvfderiv (𝓡 n) η x (b i) * g.tensorPairingCovector F T x ![b i]
  let Tw := ∑ i, mvfderiv (𝓡 n) w x (b i) * g.tensorPairingCovector F T x ![b i]
  let SF := g.tensorPairingThree F (D.covariantTensorDerivative Z) x
  let ST := g.tensorPairingThree (D.covariantTensorDerivative T) (D.covariantTensorDerivative Z) x
  have hwpos : 0 < w x := regularized_tensor_norm_pos (g := g) T hε x
  have hw2 : w x ^ 2 = g.tensorPairingTwo T T x + ε :=
    Real.sq_sqrt (Real.sqrt_pos.mp hwpos).le
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hW : 0 ≤ W := tensor_power_metric_nonneg x _
  have hE : 0 ≤ E := tensor_power_metric_nonneg x _
  have hy2 : y ^ 2 = A := Real.sq_sqrt hA
  have ha2 : a ^ 2 = B := Real.sq_sqrt hB
  have hz2 : z ^ 2 = W := Real.sq_sqrt hW
  have he2 : e ^ 2 = E := Real.sq_sqrt hE
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hz : 0 ≤ z := Real.sqrt_nonneg _
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.rpow_nonneg hwpos.le _
  have ht : 0 ≤ t := Real.rpow_nonneg hwpos.le _
  have hq : 0 ≤ 2 * p - 2 := by linarith
  have hWA : W ≤ A := D.gradient_regularized_tensor_norm_le hT hε x
  have hzy : z ≤ y := Real.sqrt_le_sqrt hWA
  have htw : t * w x = s := by
    dsimp [t, s]
    rw [← Real.rpow_add_one hwpos.ne']
    congr 1
    ring
  have hsw : w x ^ (2 * p - 1) = s * w x := by
    dsimp [s]
    rw [← Real.rpow_add_one hwpos.ne']
    congr 1
    ring
  have hsp : s * w x ^ 2 = (w x ^ p) ^ 2 := tensor_power_weight_sq hwpos p
  have hTnorm : Real.sqrt (g.tensorPairingTwo T T x) ≤ w x := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hwpos.le, by linarith⟩
  have hC : |C| ≤ a * y := g.abs_tensorPairingThree_le F (D.covariantTensorDerivative T) x
  have hTη : |Tη| ≤ e * a * w x :=
    (D.abs_gradient_tensorPairingCovector_le η F T x).trans
      (mul_le_mul_of_nonneg_left hTnorm (mul_nonneg he ha))
  have hTw : |Tw| ≤ z * a * w x :=
    (D.abs_gradient_tensorPairingCovector_le w F T x).trans
      (mul_le_mul_of_nonneg_left hTnorm (mul_nonneg hz ha))
  have hcross : |g.inner x (D.gradient η x) (D.gradient w x)| ≤ e * y := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact (tensor_power_abs_inner_le_sqrt (D.gradient η x) (D.gradient w x)).trans
      (mul_le_mul_of_nonneg_left hzy he)
  have hSF : SF = η x ^ 2 * s * C + 2 * η x * s * Tη +
      (2 * p - 2) * η x ^ 2 * t * Tw :=
    D.tensorPairingThree_derivative_regularized_power_cross F hT hη hε p x
  have hSFabs : |SF| ≤ s *
      (|η x| ^ 2 * a * y + 2 * |η x| * w x * e * a +
        (2 * p - 2) * |η x| ^ 2 * z * a) := by
    rw [hSF]
    calc
      _ ≤ |η x ^ 2 * s * C| + |2 * η x * s * Tη| +
          |(2 * p - 2) * η x ^ 2 * t * Tw| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = η x ^ 2 * s * |C| + 2 * |η x| * s * |Tη| +
          (2 * p - 2) * η x ^ 2 * t * |Tw| := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg (η x)), abs_of_nonneg hs,
          abs_of_nonneg ht, abs_of_nonneg hq, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ η x ^ 2 * s * (a * y) + 2 * |η x| * s * (e * a * w x) +
          (2 * p - 2) * η x ^ 2 * t * (z * a * w x) := by gcongr
      _ = η x ^ 2 * s * (a * y) + 2 * |η x| * s * (e * a * w x) +
          (2 * p - 2) * η x ^ 2 * (t * w x) * (z * a) := by ring
      _ = _ := by rw [htw, sq_abs]; ring
  have hcrossabs : |2 * η x * w x ^ (2 * p - 1) *
      g.inner x (D.gradient η x) (D.gradient w x)| ≤
      s * (2 * |η x| * w x * e * y) := by
    rw [hsw]
    simp only [abs_mul, abs_of_nonneg hs, abs_of_pos hwpos,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * |η x| * (s * w x) * (e * y) := by gcongr
      _ = _ := by ring
  have hST := D.tensorPairingThree_derivative_regularized_power hT hη hε p x
  change ST = η x ^ 2 * s * A + (2 * p - 2) * η x ^ 2 * s * W +
    2 * η x * w x ^ (2 * p - 1) * g.inner x (D.gradient η x) (D.gradient w x) at hST
  have habsorb := mul_le_mul_of_nonneg_left
    (tensor_power_absorption hp |η x| (w x) e y z a) hs
  rw [sq_abs, hy2, hz2, he2, ha2] at habsorb
  rw [sq_abs] at hSFabs
  have hposSF := le_abs_self SF
  have hnegcross := neg_le_abs (2 * η x * w x ^ (2 * p - 1) *
    g.inner x (D.gradient η x) (D.gradient w x))
  have hweighted := mul_le_mul_of_nonneg_left hWA (mul_nonneg (sq_nonneg (η x)) hs)
  change (p - 1 / 2) * (η x ^ 2 * s * W) ≤ ST - SF +
    5 * ((w x ^ p) ^ 2 * E) + (p + 1) * (η x ^ 2 * s * B)
  nlinarith only [hST, habsorb, hSFabs, hcrossabs, hposSF, hnegcross,
    hweighted, congrArg (fun q : ℝ => q * E) hsp]

end PoincareConjecture.LeviCivitaData

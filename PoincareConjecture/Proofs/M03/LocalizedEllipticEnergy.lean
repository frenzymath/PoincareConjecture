import PoincareConjecture.Proofs.M03.CoordinateIntegration










set_option autoImplicit false

open scoped ContDiff Topology BigOperators
open MeasureTheory Set

namespace PoincareConjecture.Proofs.M03

theorem exists_localized_elliptic_energy_bound
    {n : ℕ} {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {a : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) V)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφV : tsupport φ ⊆ V) {lambda : ℝ} (hlambda : 0 < lambda)
    (haell : ∀ x ∈ tsupport φ, ∀ z : Fin n → ℝ,
      lambda * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, a x i j * z i * z j) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ 2 f V →
      (∫ x, φ x ^ 2 * f x *
        ∑ i, fderiv ℝ
          (fun y => ∑ j, a y i j * fderiv ℝ f y (EuclideanSpace.single j 1))
          x (EuclideanSpace.single i 1)) ≤
        -(lambda / 2) * (∫ x, φ x ^ 2 *
          ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2) +
        C * (∫ x in tsupport φ, f x ^ 2) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  let e (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  let B (j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    ∑ i, fderiv ℝ φ x (e i) * a x i j
  let S (x : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ j, B j x ^ 2
  have hφd (i : Fin n) : Continuous (fun x => fderiv ℝ φ x (e i)) :=
    (hφ.continuous_fderiv (by decide)).clm_apply continuous_const
  have hB (j : Fin n) : ContinuousOn (B j) V :=
    continuousOn_finsetSum _ (fun i _ => (hφd i).continuousOn.mul (ha i j).continuousOn)
  have hS : ContinuousOn S V :=
    continuousOn_finsetSum _ (fun j _ => (hB j).pow 2)
  obtain ⟨b, hb⟩ := hφc.exists_bound_of_continuousOn (hS.mono hφV)
  have hbound : ∀ x ∈ tsupport φ, S x ≤ max b 0 := by
    intro x hx
    exact (le_abs_self (S x)).trans ((hb x hx).trans (le_max_left b 0))
  let C : ℝ := (2 / lambda) * max b 0
  have hC : 0 ≤ C := mul_nonneg (div_nonneg (by norm_num) hlambda.le) (le_max_right b 0)
  refine ⟨C, hC, ?_⟩
  intro f hf
  let p (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ := fderiv ℝ f x (e i)
  let q (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ j, a x i j * p j x
  have hp (i : Fin n) : ContDiffOn ℝ 1 (p i) V :=
    (hf.fderiv_of_isOpen hV (by norm_num)).clm_apply contDiffOn_const
  have hq (i : Fin n) : ContDiffOn ℝ 1 (q i) V :=
    ContDiffOn.sum (fun j _ => (ha i j).mul (hp j))
  have hf1 : ContDiffOn ℝ 1 f V := hf.of_le (by norm_num)
  have hpatch : ∀ Q : EuclideanSpace ℝ (Fin n) → ℝ, ContinuousOn Q V →
      (∀ x ∉ tsupport φ, Q x = 0) → Integrable Q := by
    intro Q hQ hzero
    have hQc : HasCompactSupport Q := by
      apply hφc.mono'
      intro x hx
      by_contra hxφ
      exact hx (hzero x hxφ)
    have hQc' : Continuous Q := by
      apply continuous_iff_continuousAt.mpr
      intro x
      by_cases hx : x ∈ V
      · exact hQ.continuousAt (hV.mem_nhds hx)
      · have hxφ : x ∈ (tsupport φ)ᶜ := fun h => hx (hφV h)
        apply continuousAt_const.congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxφ] with y hy
        exact hzero y hy
    exact hQc'.integrable_of_hasCompactSupport hQc
  let L (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    φ x ^ 2 * f x * fderiv ℝ (q i) x (e i)
  let R (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    (φ x ^ 2 * p i x + 2 * φ x * fderiv ℝ φ x (e i) * f x) * q i x
  let G (x : EuclideanSpace ℝ (Fin n)) : ℝ := φ x ^ 2 * ∑ i, p i x ^ 2
  have hLi (i : Fin n) : Integrable (L i) := hpatch _
    (((hφ.continuous.continuousOn.pow 2).mul hf.continuousOn).mul
      (((hq i).continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const))
    (fun x hx => by simp [L, image_eq_zero_of_notMem_tsupport hx])
  have hRi (i : Fin n) : Integrable (R i) := hpatch _
    ((((hφ.continuous.continuousOn.pow 2).mul (hp i).continuousOn).add
      (((continuousOn_const.mul hφ.continuous.continuousOn).mul
        (hφd i).continuousOn).mul hf.continuousOn)).mul (hq i).continuousOn)
    (fun x hx => by simp [R, image_eq_zero_of_notMem_tsupport hx])
  have hGi : Integrable G := hpatch _
    ((hφ.continuous.continuousOn.pow 2).mul
      (continuousOn_finsetSum _ (fun i _ => (hp i).continuousOn.pow 2)))
    (fun x hx => by simp [G, image_eq_zero_of_notMem_tsupport hx])
  have hKi : Integrable ((tsupport φ).indicator (fun x => f x ^ 2)) :=
    (ContinuousOn.integrableOn_compact hφc
      ((hf.continuousOn.pow 2).mono hφV)).integrable_indicator (isClosed_tsupport φ).measurableSet
  have hibp (i : Fin n) : (∫ x, L i x) = -(∫ x, R i x) :=
    integral_localized_mul_fderiv hV hf1 (hq i) hφ hφc hφV (e i)
  have hsum : (∫ x, ∑ i, L i x) = -(∫ x, ∑ i, R i x) := by
    rw [integral_finsetSum _ (fun i _ => hLi i), integral_finsetSum _ (fun i _ => hRi i)]
    simp only [hibp, Finset.sum_neg_distrib]
  have hRform (x : EuclideanSpace ℝ (Fin n)) : (∑ i, R i x) =
      φ x ^ 2 * (∑ i, ∑ j, a x i j * p i x * p j x) +
        2 * φ x * f x * (∑ j, B j x * p j x) := by
    have hcross : (∑ i, ∑ j, fderiv ℝ φ x (e i) * a x i j * p j x) =
        ∑ j, B j x * p j x := by
      rw [Finset.sum_comm]
      simp only [B, Finset.sum_mul]
    calc
      (∑ i, R i x) = ∑ i, ∑ j,
          (φ x ^ 2 * (a x i j * p i x * p j x) +
            2 * φ x * f x * (fderiv ℝ φ x (e i) * a x i j * p j x)) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [R, q]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = φ x ^ 2 * (∑ i, ∑ j, a x i j * p i x * p j x) +
          2 * φ x * f x * (∑ i, ∑ j, fderiv ℝ φ x (e i) * a x i j * p j x) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by rw [hcross]
  have hyoung (u v : ℝ) : -2 * u * v ≤ lambda / 2 * u ^ 2 + (2 / lambda) * v ^ 2 := by
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * lambda by positivity)).mp
    field_simp
    nlinarith [sq_nonneg (lambda * u + 2 * v)]
  have hpoint : ∀ x, -(∑ i, R i x) ≤ -(lambda / 2) * G x +
      C * (tsupport φ).indicator (fun y => f y ^ 2) x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hell := mul_le_mul_of_nonneg_left (haell x hx (fun i => p i x)) (sq_nonneg (φ x))
      have herror : -2 * φ x * f x * (∑ j, B j x * p j x) ≤
          lambda / 2 * G x + (2 / lambda) * f x ^ 2 * S x := by
        calc
          -2 * φ x * f x * (∑ j, B j x * p j x) =
              ∑ j, -2 * (φ x * p j x) * (f x * B j x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ ≤ ∑ j, (lambda / 2 * (φ x * p j x) ^ 2 +
              (2 / lambda) * (f x * B j x) ^ 2) :=
            Finset.sum_le_sum (fun j _ => hyoung (φ x * p j x) (f x * B j x))
          _ = _ := by
            dsimp only [G, S]
            simp only [mul_pow, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            ring
      have hrem : (2 / lambda) * f x ^ 2 * S x ≤ C * f x ^ 2 := by
        have h := mul_le_mul_of_nonneg_left (hbound x hx)
          (mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlambda.le) (sq_nonneg (f x)))
        dsimp only [C]
        nlinarith only [h]
      rw [hRform, indicator_of_mem hx]
      dsimp only [G] at herror ⊢
      nlinarith only [hell, herror, hrem]
    · simp [R, G, indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  change (∫ x, φ x ^ 2 * f x * ∑ i, fderiv ℝ (q i) x (e i)) ≤
    -(lambda / 2) * (∫ x, G x) + C * (∫ x in tsupport φ, f x ^ 2)
  have hleft : (∫ x, φ x ^ 2 * f x * ∑ i, fderiv ℝ (q i) x (e i)) =
      ∫ x, ∑ i, L i x := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [L, Finset.mul_sum]
  rw [hleft, hsum, ← integral_neg]
  calc
    (∫ x, -(∑ i, R i x)) ≤ ∫ x, -(lambda / 2) * G x +
        C * (tsupport φ).indicator (fun y => f y ^ 2) x :=
      integral_mono (integrable_finsetSum _ (fun i _ => hRi i)).neg
        ((hGi.const_mul _).add (hKi.const_mul _)) hpoint
    _ = _ := by
      rw [integral_add (hGi.const_mul _) (hKi.const_mul _),
        integral_const_mul, integral_const_mul, integral_indicator (isClosed_tsupport φ).measurableSet]

end PoincareConjecture.Proofs.M03

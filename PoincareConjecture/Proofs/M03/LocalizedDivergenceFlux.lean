import PoincareConjecture.Proofs.M03.CoordinateIntegration










set_option autoImplicit false

open scoped ContDiff Topology BigOperators
open MeasureTheory Set

namespace PoincareConjecture.Proofs.M03

theorem exists_localized_divergence_flux_bound
    {n : ℕ} {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφV : tsupport φ ⊆ V) :
    letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
    letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
    ∃ A : ℝ, 0 ≤ A ∧ ∀ epsilon : ℝ, 0 < epsilon →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ 1 f V →
      ∀ U : EuclideanSpace ℝ (Fin n) → Fin n → ℝ,
      (∀ i, ContDiffOn ℝ 1 (fun x => U x i) V) →
      (∫ x, φ x ^ 2 * f x *
        ∑ i, fderiv ℝ (fun y => U y i) x (EuclideanSpace.single i 1)) ≤
        epsilon * (∫ x, φ x ^ 2 *
          ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2) +
        A * (∫ x in tsupport φ, f x ^ 2) +
        (1 + 1 / (4 * epsilon)) * (∫ x, φ x ^ 2 * ∑ i, (U x i) ^ 2) := by
  let : MeasurableSpace (EuclideanSpace ℝ (Fin n)) := borel _
  let : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  classical
  let e (i : Fin n) : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  let d (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ := fderiv ℝ φ x (e i)
  let S (x : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i, d i x ^ 2
  have hd (i : Fin n) : Continuous (d i) :=
    (hφ.continuous_fderiv (by decide)).clm_apply continuous_const
  have hS : Continuous S := continuous_finsetSum _ (fun i _ => (hd i).pow 2)
  obtain ⟨b, hb⟩ := hφc.exists_bound_of_continuousOn hS.continuousOn
  let A : ℝ := max b 0
  have hbound : ∀ x ∈ tsupport φ, S x ≤ A := by
    intro x hx
    exact (le_abs_self (S x)).trans ((hb x hx).trans (le_max_left b 0))
  refine ⟨A, le_max_right b 0, ?_⟩
  intro epsilon hepsilon f hf U hU
  let p (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ := fderiv ℝ f x (e i)
  have hp (i : Fin n) : ContinuousOn (p i) V :=
    (hf.continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const
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
    φ x ^ 2 * f x * fderiv ℝ (fun y => U y i) x (e i)
  let R (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    (φ x ^ 2 * p i x + 2 * φ x * d i x * f x) * U x i
  let G (x : EuclideanSpace ℝ (Fin n)) : ℝ := φ x ^ 2 * ∑ i, p i x ^ 2
  let H (x : EuclideanSpace ℝ (Fin n)) : ℝ := φ x ^ 2 * ∑ i, (U x i) ^ 2
  have hLi (i : Fin n) : Integrable (L i) := hpatch _
    (((hφ.continuous.continuousOn.pow 2).mul hf.continuousOn).mul
      (((hU i).continuousOn_fderiv_of_isOpen hV le_rfl).clm_apply continuousOn_const))
    (fun x hx => by simp [L, image_eq_zero_of_notMem_tsupport hx])
  have hRi (i : Fin n) : Integrable (R i) := hpatch _
    ((((hφ.continuous.continuousOn.pow 2).mul (hp i)).add
      (((continuousOn_const.mul hφ.continuous.continuousOn).mul
        (hd i).continuousOn).mul hf.continuousOn)).mul (hU i).continuousOn)
    (fun x hx => by simp [R, image_eq_zero_of_notMem_tsupport hx])
  have hGi : Integrable G := hpatch _
    ((hφ.continuous.continuousOn.pow 2).mul
      (continuousOn_finsetSum _ (fun i _ => (hp i).pow 2)))
    (fun x hx => by simp [G, image_eq_zero_of_notMem_tsupport hx])
  have hHi : Integrable H := hpatch _
    ((hφ.continuous.continuousOn.pow 2).mul
      (continuousOn_finsetSum _ (fun i _ => (hU i).continuousOn.pow 2)))
    (fun x hx => by simp [H, image_eq_zero_of_notMem_tsupport hx])
  have hKi : Integrable ((tsupport φ).indicator (fun x => f x ^ 2)) :=
    (ContinuousOn.integrableOn_compact hφc
      ((hf.continuousOn.pow 2).mono hφV)).integrable_indicator (isClosed_tsupport φ).measurableSet
  have hibp (i : Fin n) : (∫ x, L i x) = -(∫ x, R i x) :=
    integral_localized_mul_fderiv hV hf (hU i) hφ hφc hφV (e i)
  have hsum : (∫ x, ∑ i, L i x) = -(∫ x, ∑ i, R i x) := by
    rw [integral_finsetSum _ (fun i _ => hLi i), integral_finsetSum _ (fun i _ => hRi i)]
    simp only [hibp, Finset.sum_neg_distrib]
  have hyoung (u v : ℝ) : -u * v ≤ epsilon * u ^ 2 + (1 / (4 * epsilon)) * v ^ 2 := by
    apply (mul_le_mul_iff_left₀ (show 0 < 4 * epsilon by positivity)).mp
    field_simp
    nlinarith [sq_nonneg (2 * epsilon * u + v)]
  have hpoint : ∀ x, -(∑ i, R i x) ≤ epsilon * G x +
      A * (tsupport φ).indicator (fun y => f y ^ 2) x +
      (1 + 1 / (4 * epsilon)) * H x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hterm (i : Fin n) : -R i x ≤ epsilon * (φ x * p i x) ^ 2 +
          (f x * d i x) ^ 2 + (1 + 1 / (4 * epsilon)) * (φ x * U x i) ^ 2 := by
        have hfirst := hyoung (φ x * p i x) (φ x * U x i)
        have hsecond := sq_nonneg (f x * d i x + φ x * U x i)
        dsimp only [R]
        nlinarith only [hfirst, hsecond]
      have htotal : -(∑ i, R i x) ≤ epsilon * G x + f x ^ 2 * S x +
          (1 + 1 / (4 * epsilon)) * H x := by
        calc
          -(∑ i, R i x) = ∑ i, -R i x := by rw [Finset.sum_neg_distrib]
          _ ≤ ∑ i, (epsilon * (φ x * p i x) ^ 2 + (f x * d i x) ^ 2 +
              (1 + 1 / (4 * epsilon)) * (φ x * U x i) ^ 2) :=
            Finset.sum_le_sum (fun i _ => hterm i)
          _ = _ := by
            simp only [G, H, S, mul_pow, Finset.sum_add_distrib, Finset.mul_sum]
      have hrem := mul_le_mul_of_nonneg_left (hbound x hx) (sq_nonneg (f x))
      rw [indicator_of_mem hx]
      nlinarith only [htotal, hrem]
    · simp [R, G, H, indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  change (∫ x, φ x ^ 2 * f x * ∑ i, fderiv ℝ (fun y => U y i) x (e i)) ≤
    epsilon * (∫ x, G x) + A * (∫ x in tsupport φ, f x ^ 2) +
      (1 + 1 / (4 * epsilon)) * (∫ x, H x)
  have hleft : (∫ x, φ x ^ 2 * f x * ∑ i, fderiv ℝ (fun y => U y i) x (e i)) =
      ∫ x, ∑ i, L i x := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [L, Finset.mul_sum]
  rw [hleft, hsum, ← integral_neg]
  calc
    (∫ x, -(∑ i, R i x)) ≤ ∫ x, epsilon * G x +
        A * (tsupport φ).indicator (fun y => f y ^ 2) x + (1 + 1 / (4 * epsilon)) * H x :=
      integral_mono (integrable_finsetSum _ (fun i _ => hRi i)).neg
        (((hGi.const_mul _).add (hKi.const_mul _)).add (hHi.const_mul _)) hpoint
    _ = _ := by
      have hsumI : Integrable (fun x => epsilon * G x +
          A * (tsupport φ).indicator (fun y => f y ^ 2) x) :=
        (hGi.const_mul _).add (hKi.const_mul _)
      rw [integral_add hsumI (hHi.const_mul _),
        integral_add (hGi.const_mul _) (hKi.const_mul _),
        integral_const_mul, integral_const_mul, integral_const_mul,
        integral_indicator (isClosed_tsupport φ).measurableSet]

end PoincareConjecture.Proofs.M03

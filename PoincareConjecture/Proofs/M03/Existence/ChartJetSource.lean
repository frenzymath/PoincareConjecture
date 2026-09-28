import PoincareConjecture.Proofs.M03.Existence.DeTurckSymbol
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Instances.Matrix










set_option autoImplicit false

noncomputable section

open scoped ContDiff Matrix.Norms.Elementwise

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ}


structure MetricJet2 where
  value : Matrix (Fin n) (Fin n) ℝ
  first : Fin n → Matrix (Fin n) (Fin n) ℝ
  second : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ


def coordinateMetricJet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : Fin n → V) (G : V → Matrix (Fin n) (Fin n) ℝ) (y : V) :
    MetricJet2 (n := n) :=
  { value := G y
    first := fun a i j => fderiv ℝ (fun z => G z i j) y (e a)
    second := fun a b i j =>
      fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z (e b)) y (e a) }

theorem coordinateMetricJet_value_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : Fin n → V) (G : V → Matrix (Fin n) (Fin n) ℝ)
    {U : Set V} (hU : IsOpen U)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun y => G y i j) U) :
    ContDiffOn ℝ ∞ (fun y => (coordinateMetricJet e G y).value) U := by
  exact contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => hG i j

theorem coordinateMetricJet_first_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : Fin n → V) (G : V → Matrix (Fin n) (Fin n) ℝ)
    {U : Set V} (hU : IsOpen U)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun y => G y i j) U) :
    ContDiffOn ℝ ∞
      (fun y => (coordinateMetricJet e G y).first)
      U := by
  have hfirst (a i j : Fin n) :
      ContDiffOn ℝ ∞
        (fun y => fderiv ℝ (fun z => G z i j) y (e a)) U :=
    ((hG i j).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  apply contDiffOn_pi.mpr
  intro a
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_pi.mpr fun j => hfirst a i j

theorem coordinateMetricJet_second_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (e : Fin n → V) (G : V → Matrix (Fin n) (Fin n) ℝ)
    {U : Set V} (hU : IsOpen U)
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun y => G y i j) U) :
    ContDiffOn ℝ ∞
      (fun y => (coordinateMetricJet e G y).second)
      U := by
  have hfirst (a i j : Fin n) :
      ContDiffOn ℝ ∞
        (fun y => fderiv ℝ (fun z => G z i j) y (e a)) U :=
    ((hG i j).fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hsecond (a b i j : Fin n) :
      ContDiffOn ℝ ∞
        (fun y => fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z (e b)) y
          (e a)) U := by
    exact ((hfirst b i j).fderiv_of_isOpen hU (by simp)).clm_apply
      contDiffOn_const
  apply contDiffOn_pi.mpr
  intro a
  apply contDiffOn_pi.mpr
  intro b
  apply contDiffOn_pi.mpr
  intro i
  exact contDiffOn_pi.mpr fun j => hsecond a b i j




def secondJetSource (G : Matrix (Fin n) (Fin n) ℝ)
    (H : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : ℝ :=
  ∑ a, ∑ b, G⁻¹ a b * H a b i j


def eraseSecondJet (q : MetricJet2 (n := n)) : MetricJet2 (n := n) :=
  { value := q.value, first := q.first, second := 0 }




def lowerOrderSource (background : MetricJet2 (n := n))
    (q : MetricJet2 (n := n)) (i j : Fin n) : ℝ :=
  ∑ a, (q.first a i j - background.first a i j)


def chartSource (background q : MetricJet2 (n := n)) (i j : Fin n) : ℝ :=
  secondJetSource q.value q.second i j + lowerOrderSource background q i j


def nonsingularMetricJets : Set (MetricJet2 (n := n)) :=
  {q | q.value.det ≠ 0}






def christoffelJet (q : MetricJet2 (n := n)) (k i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, q.value⁻¹ k l *
    (q.first i l j + q.first j l i - q.first l i j)


def inverseFirst (q : MetricJet2 (n := n)) (a k l : Fin n) : ℝ :=
  -∑ u, ∑ v, q.value⁻¹ k u * q.first a u v * q.value⁻¹ v l


def christoffelSecond (q : MetricJet2 (n := n))
    (a k i j : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l,
    (inverseFirst q a k l *
        (q.first i l j + q.first j l i - q.first l i j) +
      q.value⁻¹ k l *
        (q.second a i l j + q.second a j l i - q.second a l i j))


def mixedCurvatureJet (q : MetricJet2 (n := n))
    (i j k l : Fin n) : ℝ :=
  christoffelSecond q i l j k - christoffelSecond q j l i k +
    ∑ m, (christoffelJet q m j k * christoffelJet q l i m -
      christoffelJet q m i k * christoffelJet q l j m)


def ricciJet (q : MetricJet2 (n := n)) (i j : Fin n) : ℝ :=
  ∑ k, mixedCurvatureJet q k i j k


def deTurckVector (background q : MetricJet2 (n := n)) (k : Fin n) : ℝ :=
  ∑ a, ∑ b, q.value⁻¹ a b *
    (christoffelJet q k a b - christoffelJet background k a b)


def deTurckVectorFirst (background q : MetricJet2 (n := n))
    (a k : Fin n) : ℝ :=
  ∑ u, ∑ v,
      (inverseFirst q a u v *
        (christoffelJet q k u v - christoffelJet background k u v) +
      q.value⁻¹ u v *
        (christoffelSecond q a k u v - christoffelSecond background a k u v))


def lieDerivativeJet (background q : MetricJet2 (n := n)) (i j : Fin n) : ℝ :=
  ∑ k,
    (deTurckVector background q k * q.first k i j +
      q.value k j * deTurckVectorFirst background q i k +
      q.value i k * deTurckVectorFirst background q j k)


def ricciDeTurckSource (background q : MetricJet2 (n := n))
    (i j : Fin n) : ℝ :=
  -2 * ricciJet q i j + lieDerivativeJet background q i j



def secondJetChristoffel (A : Matrix (Fin n) (Fin n) ℝ)
    (H : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (a i j k : Fin n) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, A k l *
    (H a i l j + H a j l i - H a l i j)


def ricciDeTurckSecondJet (G : Matrix (Fin n) (Fin n) ℝ)
    (H : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : ℝ :=
  -2 * ∑ k, (secondJetChristoffel G⁻¹ H k i j k -
      secondJetChristoffel G⁻¹ H i k j k) +
    ∑ k, (G k j * (∑ a, ∑ b, G⁻¹ a b *
        secondJetChristoffel G⁻¹ H i a b k) +
      G i k * (∑ a, ∑ b, G⁻¹ a b *
        secondJetChristoffel G⁻¹ H j a b k))

private theorem symmetric_weighted_sum_swap
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (F : Fin n → Fin n → ℝ) :
    (∑ k, ∑ l, A k l * F l k) = ∑ k, ∑ l, A k l * F k l := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hA.apply]

private theorem secondJetChristoffel_trace
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (H : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (a j : Fin n) :
    (∑ k, secondJetChristoffel A H a k j k) =
      (1 / 2 : ℝ) * ∑ k, ∑ l, A k l * H a j k l := by
  have hswap := symmetric_weighted_sum_swap A hA (fun k l => H a k l j)
  have htrace := symmetric_weighted_sum_swap A hA (fun k l => H a j k l)
  calc
    _ = (1 / 2 : ℝ) * ((∑ k, ∑ l, A k l * H a k l j) +
        (∑ k, ∑ l, A k l * H a j l k) -
        (∑ k, ∑ l, A k l * H a l k j)) := by
      simp only [secondJetChristoffel, Finset.mul_sum, mul_add, mul_sub,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = _ := by rw [hswap, htrace]; ring

private theorem lower_secondJetChristoffel
    (G : Matrix (Fin n) (Fin n) ℝ) (hdet : G.det ≠ 0)
    (H : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (a i j r : Fin n) :
    (∑ k, G r k * secondJetChristoffel G⁻¹ H a i j k) =
      (1 / 2 : ℝ) * (H a i r j + H a j r i - H a r i j) := by
  have hid (l : Fin n) : (∑ k, G r k * G⁻¹ k l) =
      if r = l then 1 else 0 := by
    change (G * G⁻¹) r l = _
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)]
    simp [Matrix.one_apply]
  calc
    _ = (1 / 2 : ℝ) * ∑ l, (∑ k, G r k * G⁻¹ k l) *
        (H a i l j + H a j l i - H a l i j) := by
      simp only [secondJetChristoffel, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by simp [hid]

private theorem lower_trace_secondJetChristoffel
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm)
    (hdet : G.det ≠ 0)
    (H : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hH : ∀ a b i j, H a b i j = H a b j i) (a r : Fin n) :
    (∑ k, G r k * (∑ i, ∑ j, G⁻¹ i j *
      secondJetChristoffel G⁻¹ H a i j k)) =
      ∑ i, ∑ j, G⁻¹ i j *
        (H a i j r - (1 / 2 : ℝ) * H a r i j) := by
  have hswap := symmetric_weighted_sum_swap G⁻¹ hG.inv
    (fun i j => H a i j r)
  calc
    _ = ∑ i, ∑ j, G⁻¹ i j *
        (∑ k, G r k * secondJetChristoffel G⁻¹ H a i j k) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = (1 / 2 : ℝ) * ((∑ i, ∑ j, G⁻¹ i j * H a i j r) +
        (∑ i, ∑ j, G⁻¹ i j * H a j i r) -
        (∑ i, ∑ j, G⁻¹ i j * H a r i j)) := by
      simp_rw [lower_secondJetChristoffel G hdet H, hH a _ r _]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [hswap]
      have hfactor : (∑ i, ∑ j, G⁻¹ i j * ((1 / 2 : ℝ) * H a r i j)) =
          (1 / 2 : ℝ) * ∑ i, ∑ j, G⁻¹ i j * H a r i j := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hfactor]
      ring

theorem ricciDeTurckSecondJet_eq
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.IsSymm)
    (hdet : G.det ≠ 0)
    (H : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hHm : ∀ a b i j, H a b i j = H a b j i)
    (hHd : ∀ a b i j, H a b i j = H b a i j) (i j : Fin n) :
    ricciDeTurckSecondJet G H i j =
      ∑ a, ∑ b, G⁻¹ a b * H a b i j := by
  have hmetric (k : Fin n) : G k j = G j k := hG.apply j k
  unfold ricciDeTurckSecondJet
  simp_rw [hmetric]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    secondJetChristoffel_trace G⁻¹ hG.inv,
    lower_trace_secondJetChristoffel G hG hdet H hHm,
    lower_trace_secondJetChristoffel G hG hdet H hHm]
  simp only [secondJetChristoffel, Finset.mul_sum, mul_sub,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hHd a i, hHd a j, hHd j i]
  ring

@[simp] theorem christoffelJet_eraseSecondJet
    (q : MetricJet2 (n := n)) (k i j : Fin n) :
    christoffelJet (eraseSecondJet q) k i j = christoffelJet q k i j := rfl

@[simp] theorem inverseFirst_eraseSecondJet
    (q : MetricJet2 (n := n)) (a i j : Fin n) :
    inverseFirst (eraseSecondJet q) a i j = inverseFirst q a i j := rfl

@[simp] theorem deTurckVector_eraseSecondJet
    (background q : MetricJet2 (n := n)) (k : Fin n) :
    deTurckVector background (eraseSecondJet q) k =
      deTurckVector background q k := rfl

theorem christoffelSecond_split
    (q : MetricJet2 (n := n)) (a k i j : Fin n) :
    christoffelSecond q a k i j =
      secondJetChristoffel q.value⁻¹ q.second a i j k +
        christoffelSecond (eraseSecondJet q) a k i j := by
  simp only [christoffelSecond, secondJetChristoffel, eraseSecondJet,
    inverseFirst, Pi.zero_apply, Matrix.zero_apply, add_zero, sub_zero,
    mul_zero, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem ricciJet_split
    (q : MetricJet2 (n := n)) (i j : Fin n) :
    ricciJet q i j =
      (∑ k, (secondJetChristoffel q.value⁻¹ q.second k i j k -
        secondJetChristoffel q.value⁻¹ q.second i k j k)) +
        ricciJet (eraseSecondJet q) i j := by
  unfold ricciJet mixedCurvatureJet
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [christoffelJet_eraseSecondJet]
  rw [christoffelSecond_split q k k i j,
    christoffelSecond_split q i k k j]
  ring

private theorem deTurckVectorFirst_split
    (background q : MetricJet2 (n := n)) (a k : Fin n) :
    deTurckVectorFirst background q a k =
      (∑ i, ∑ j, q.value⁻¹ i j *
        secondJetChristoffel q.value⁻¹ q.second a i j k) +
        deTurckVectorFirst background (eraseSecondJet q) a k := by
  unfold deTurckVectorFirst
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [inverseFirst_eraseSecondJet, christoffelJet_eraseSecondJet]
  rw [christoffelSecond_split q a k i j]
  change _ = _ + (inverseFirst q a i j *
    (christoffelJet q k i j - christoffelJet background k i j) +
      q.value⁻¹ i j *
        (christoffelSecond (eraseSecondJet q) a k i j -
          christoffelSecond background a k i j))
  ring


theorem ricciDeTurckSource_split
    (background q : MetricJet2 (n := n)) (i j : Fin n) :
    ricciDeTurckSource background q i j =
      ricciDeTurckSecondJet q.value q.second i j +
        ricciDeTurckSource background (eraseSecondJet q) i j := by
  unfold ricciDeTurckSource ricciDeTurckSecondJet lieDerivativeJet
  rw [ricciJet_split q]
  simp only [deTurckVectorFirst_split background q,
    deTurckVector_eraseSecondJet]
  change -2 * (_ + ricciJet (eraseSecondJet q) i j) +
      (∑ k, (deTurckVector background q k * q.first k i j +
        q.value k j * (_ + deTurckVectorFirst background (eraseSecondJet q) i k) +
        q.value i k * (_ + deTurckVectorFirst background (eraseSecondJet q) j k))) = _
  simp only [mul_add, Finset.sum_add_distrib]
  dsimp only [eraseSecondJet]
  ring



theorem ricciDeTurckSource_quasilinear
    (background q : MetricJet2 (n := n))
    (hG : q.value.IsSymm) (hdet : q.value.det ≠ 0)
    (hHm : ∀ a b i j, q.second a b i j = q.second a b j i)
    (hHd : ∀ a b i j, q.second a b i j = q.second b a i j)
    (i j : Fin n) :
    ricciDeTurckSource background q i j =
      (∑ a, ∑ b, q.value⁻¹ a b * q.second a b i j) +
        ricciDeTurckSource background (eraseSecondJet q) i j := by
  rw [ricciDeTurckSource_split,
    ricciDeTurckSecondJet_eq q.value hG hdet q.second hHm hHd]


def ricciDeTurckLowerOrder (background q : MetricJet2 (n := n))
    (i j : Fin n) : ℝ :=
  ricciDeTurckSource background q i j - secondJetSource q.value q.second i j

theorem ricciDeTurckSource_decomp (background q : MetricJet2 (n := n))
    (i j : Fin n) :
    ricciDeTurckSource background q i j =
      secondJetSource q.value q.second i j +
        ricciDeTurckLowerOrder background q i j := by
  simp only [ricciDeTurckLowerOrder]
  ring




theorem continuousAt_matrix_inv_of_posDef
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) G := by
  apply continuousAt_matrix_inv G
  have hdetne : G.det ≠ 0 := (G.isUnit_iff_isUnit_det.mp hG.isUnit).ne_zero
  have hi : ContinuousAt Inv.inv G.det := NormedField.continuousAt_inv.mpr hdetne
  simpa only [Ring.inverse_eq_inv'] using hi

theorem continuousAt_matrix_inv_of_nonsingular
    (G : Matrix (Fin n) (Fin n) ℝ) (hdet : G.det ≠ 0) :
    ContinuousAt (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) G := by
  apply continuousAt_matrix_inv G
  have hi : ContinuousAt Inv.inv G.det := NormedField.continuousAt_inv.mpr hdet
  simpa only [Ring.inverse_eq_inv'] using hi

theorem continuousOn_matrix_inv_nonsingular :
    ContinuousOn (fun G : Matrix (Fin n) (Fin n) ℝ => G⁻¹)
      {G | G.det ≠ 0} := by
  intro G hG
  exact (continuousAt_matrix_inv_of_nonsingular G hG).continuousWithinAt

theorem secondJetSource_zero (G : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    secondJetSource G (0 : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ) i j = 0 := by
  simp [secondJetSource]

theorem chartSource_eraseSecondJet (background q : MetricJet2 (n := n))
    (i j : Fin n) :
    chartSource background q i j =
      secondJetSource q.value q.second i j + chartSource background (eraseSecondJet q) i j := by
  simp only [chartSource, eraseSecondJet, secondJetSource_zero, lowerOrderSource]
  ring

theorem secondJetSource_add (G : Matrix (Fin n) (Fin n) ℝ)
    (H K : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    secondJetSource G (fun a b ↦ H a b + K a b) i j =
      secondJetSource G H i j + secondJetSource G K i j := by
  simp only [secondJetSource, Pi.add_apply, Matrix.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem secondJetSource_smul (G : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ) (H : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    secondJetSource G (fun a b ↦ c • H a b) i j =
      c * secondJetSource G H i j := by
  simp only [secondJetSource, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem secondJetSource_eq_quadratic_on_slot
    (G : Matrix (Fin n) (Fin n) ℝ) (xi : Fin n → ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    quadratic G xi * H i j =
      ∑ a, ∑ b, G a b * xi a * xi b * H i j := by
  simp [quadratic, Finset.sum_mul]

theorem principal_symbol_positive_on_slot
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef)
    (xi : Fin n → ℝ) (hxi : xi ≠ 0)
    (H : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n)
    (hH : 0 < H i j) :
    0 < quadratic G xi * H i j := by
  exact mul_pos (quadratic_pos G hG xi hxi) hH

end PoincareConjecture.DeTurckNative

import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.DeTurckDifference











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness

open DeTurckNative

variable {n : ℕ}

def flatMetricJet : MetricJet2 (n := n) := ⟨1, 0, 0⟩



def normalCovariantSecondJet (b q : MetricJet2 (n := n)) : MetricSecondJet n :=
  fun a c i j => q.second a c i j -
    ∑ k, (christoffelSecond b a k c i * q.value k j +
      christoffelSecond b a k c j * q.value i k)

def normalCurvatureSource (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (p : MetricLowerJet n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k, ∑ a, ∑ c, p.1⁻¹ a c *
    (p.1 k j * R a i c k + p.1 i k * R a j c k)

def normalLowerJetSource (R : Fin n → Fin n → Fin n → Fin n → ℝ)
    (p : MetricLowerJet n) : Matrix (Fin n) (Fin n) ℝ :=
  lowerJetSource flatMetricJet p + normalCurvatureSource R p

theorem christoffelJet_eq_zero_of_first_zero (b : MetricJet2 (n := n))
    (hb : b.first = 0) (k i j : Fin n) : christoffelJet b k i j = 0 := by
  simp [christoffelJet, hb]

theorem normal_christoffelSecond_symm (b : MetricJet2 (n := n))
    (hb : b.first = 0)
    (hs : ∀ a c i j, b.second a c i j = b.second a c j i)
    (a k i j : Fin n) :
    christoffelSecond b a k i j = christoffelSecond b a k j i := by
  simp only [christoffelSecond, hb, Pi.zero_apply, Matrix.zero_apply, add_zero,
    sub_zero, mul_zero, zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [hs a l i j, add_comm (b.second a i l j) (b.second a j l i)]

private theorem flat_christoffel (k i j : Fin n) :
    christoffelJet (flatMetricJet : MetricJet2 (n := n)) k i j = 0 :=
  christoffelJet_eq_zero_of_first_zero _ rfl k i j

private theorem flat_christoffelSecond (a k i j : Fin n) :
    christoffelSecond (flatMetricJet : MetricJet2 (n := n)) a k i j = 0 := by
  simp [christoffelSecond, flatMetricJet]

private theorem normal_deTurckVector (b q : MetricJet2 (n := n))
    (hb : b.first = 0) (k : Fin n) :
    deTurckVector b q k = deTurckVector flatMetricJet q k := by
  simp only [deTurckVector, christoffelJet_eq_zero_of_first_zero b hb,
    flat_christoffel]

private theorem normal_deTurckVectorFirst (b q : MetricJet2 (n := n))
    (hb : b.first = 0) (a k : Fin n) :
    deTurckVectorFirst b q a k = deTurckVectorFirst flatMetricJet q a k -
      ∑ u, ∑ v, q.value⁻¹ u v * christoffelSecond b a k u v := by
  simp only [deTurckVectorFirst, christoffelJet_eq_zero_of_first_zero b hb,
    flat_christoffel, flat_christoffelSecond, sub_zero, mul_sub,
    ← add_sub_assoc, Finset.sum_sub_distrib]

private theorem normal_source_sub_flat (b q : MetricJet2 (n := n))
    (hb : b.first = 0) (i j : Fin n) :
    ricciDeTurckSource b q i j = ricciDeTurckSource flatMetricJet q i j -
      ∑ k, (q.value k j * (∑ a, ∑ c, q.value⁻¹ a c * christoffelSecond b i k a c) +
        q.value i k * (∑ a, ∑ c, q.value⁻¹ a c * christoffelSecond b j k a c)) := by
  simp only [ricciDeTurckSource, lieDerivativeJet, normal_deTurckVector b q hb,
    normal_deTurckVectorFirst b q hb, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

private theorem normal_connection_cancellation (b q : MetricJet2 (n := n))
    (hb : b.first = 0)
    (hs : ∀ a c i j, b.second a c i j = b.second a c j i)
    (i j : Fin n) :
    (∑ a, ∑ c, q.value⁻¹ a c *
      (∑ k, (christoffelSecond b a k c i * q.value k j +
        christoffelSecond b a k c j * q.value i k))) -
      (∑ k, (q.value k j * (∑ a, ∑ c, q.value⁻¹ a c * christoffelSecond b i k a c) +
        q.value i k * (∑ a, ∑ c, q.value⁻¹ a c * christoffelSecond b j k a c))) =
      normalCurvatureSource (mixedCurvatureJet b) (q.value, q.first) i j := by
  have hswap : (∑ a, ∑ c, q.value⁻¹ a c *
      (∑ k, (christoffelSecond b a k c i * q.value k j +
        christoffelSecond b a k c j * q.value i k))) =
      ∑ k, ∑ a, ∑ c, q.value⁻¹ a c *
        (christoffelSecond b a k c i * q.value k j +
          christoffelSecond b a k c j * q.value i k) := by
    simp only [Finset.mul_sum]
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hswap]
  simp only [normalCurvatureSource, mixedCurvatureJet,
    christoffelJet_eq_zero_of_first_zero b hb, mul_zero, sub_self,
    Finset.sum_const_zero, add_zero]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [normal_christoffelSecond_symm b hb hs a k c i,
    normal_christoffelSecond_symm b hb hs a k c j]
  ring



theorem native_source_normal_covariant (b q : MetricJet2 (n := n))
    (hb : b.first = 0)
    (hbs : ∀ a c i j, b.second a c i j = b.second a c j i)
    (hq : q.value.PosDef)
    (hqm : ∀ a c i j, q.second a c i j = q.second a c j i)
    (hqd : ∀ a c i j, q.second a c i j = q.second c a i j) (i j : Fin n) :
    ricciDeTurckSource b q i j =
      lowerJetContraction q.value⁻¹ (normalCovariantSecondJet b q) i j +
        normalLowerJetSource (mixedCurvatureJet b) (q.value, q.first) i j := by
  have hsym : q.value.IsSymm := by
    simpa only [Matrix.isHermitian_iff_isSymm] using hq.isHermitian
  have hflat := ricciDeTurckSource_quasilinear flatMetricJet q hsym
    (q.value.isUnit_iff_isUnit_det.mp hq.isUnit).ne_zero hqm hqd i j
  have hcancel := normal_connection_cancellation b q hb hbs i j
  rw [normal_source_sub_flat b q hb, hflat]
  change secondJetSource q.value q.second i j +
      lowerJetSource flatMetricJet (q.value, q.first) i j - _ = _
  simp only [lowerJetContraction, normalCovariantSecondJet, mul_sub,
    Finset.sum_sub_distrib, secondJetSource, normalLowerJetSource, Matrix.add_apply]
  linarith only [hcancel]

end PoincareConjecture.M35.Uniqueness

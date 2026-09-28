import PoincareConjecture.Proofs.M03.Existence.DeTurckSourceJetNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetAffineNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckQuasilinearEstimateNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckMetricProducerNative







set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.DeTurckPrincipalForcingNative

open DeTurckRationalJetNative DeTurckSourceJetNative DeTurckQuasilinearEstimateNative
open DeTurckJetAffineNative TensorProbeNative

universe u v

variable {iota : Type u} {n : ℕ} [Fintype iota]

def inverseDifferenceExpr (a b : Fin n) : Expr iota n :=
  .add (.atom (.inverse false a b)) (.neg (.atom (.inverse true a b)))

def metricDifferenceExpr (word : List iota) (i j : Fin n) : Expr iota n :=
  .add (.atom (.metric false word i j)) (.neg (.atom (.metric true word i j)))

def principalTermExpr (e : Fin n → iota) (a b i j : Fin n) : Expr iota n :=
  .mul (inverseDifferenceExpr a b) (metricDifferenceExpr [e a, e b] i j)

def principalTermTopExpr (e : Fin n → iota) (a b i j : Fin n)
    (word : List iota) : Expr iota n :=
  .mul (inverseDifferenceExpr a b) (metricDifferenceExpr (word ++ [e a, e b]) i j)

def principalTermTailExpr (e : Fin n → iota) (a b i j : Fin n)
    (word : List iota) : Expr iota n :=
  Expr.sumList (differentiatedCoefficientSplits word) (fun p =>
    .mul ((inverseDifferenceExpr a b).orderedDerivative p.1)
      (metricDifferenceExpr (p.2 ++ [e a, e b]) i j))

@[simp] theorem degree_inverseDifferenceExpr (a b : Fin n) :
    (inverseDifferenceExpr (iota := iota) a b).degree = 0 := by
  simp [inverseDifferenceExpr, Expr.degree, Atom.weight]

@[simp] theorem metricOrder_inverseDifferenceExpr (a b : Fin n) (label : Bool) :
    (inverseDifferenceExpr (iota := iota) a b).metricOrder label = 0 := by
  simp [inverseDifferenceExpr, Expr.metricOrder]

@[simp] theorem degree_metricDifferenceExpr (word : List iota) (i j : Fin n) :
    (metricDifferenceExpr word i j).degree = word.length := by
  simp [metricDifferenceExpr, Expr.degree, Atom.weight]

@[simp] theorem metricOrder_metricDifferenceExpr
    (word : List iota) (i j : Fin n) (label : Bool) :
    (metricDifferenceExpr word i j).metricOrder label = word.length := by
  cases label <;> simp [metricDifferenceExpr, Expr.metricOrder]

theorem orderedDerivative_metricDifferenceExpr
    (headWord suffix : List iota) (i j : Fin n) :
    (metricDifferenceExpr suffix i j).orderedDerivative headWord =
      metricDifferenceExpr (headWord ++ suffix) i j := by
  induction headWord with
  | nil => rfl
  | cons a headWord ih =>
    change Expr.derivative a ((metricDifferenceExpr suffix i j).orderedDerivative headWord) = _
    rw [ih]
    rfl


theorem degree_principalTermTailExpr_le (e : Fin n → iota)
    (a b i j : Fin n) (word : List iota) :
    (principalTermTailExpr e a b i j word).degree ≤ word.length + 2 := by
  apply Expr.degree_sumList_le
  intro p hp
  obtain ⟨hpos, hlen⟩ := differentiatedCoefficientSplits_order word p hp
  have hcoeff := Expr.degree_orderedDerivative_le p.1
    (inverseDifferenceExpr (iota := iota) a b)
  simp only [degree_inverseDifferenceExpr, zero_add] at hcoeff
  change ((inverseDifferenceExpr a b).orderedDerivative p.1).degree +
    (metricDifferenceExpr (p.2 ++ [e a, e b]) i j).degree ≤ _
  rw [degree_metricDifferenceExpr]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega


theorem metricOrder_principalTermTailExpr_le (e : Fin n → iota)
    (a b i j : Fin n) (word : List iota) (label : Bool) :
    (principalTermTailExpr e a b i j word).metricOrder label ≤ word.length + 1 := by
  apply Expr.metricOrder_sumList_le
  intro p hp
  obtain ⟨hpos, hlen⟩ := differentiatedCoefficientSplits_order word p hp
  have hcoeff := Expr.metricOrder_orderedDerivative_le p.1
    (inverseDifferenceExpr (iota := iota) a b) label
  simp only [metricOrder_inverseDifferenceExpr, zero_add] at hcoeff
  change max (((inverseDifferenceExpr a b).orderedDerivative p.1).metricOrder label)
    ((metricDifferenceExpr (p.2 ++ [e a, e b]) i j).metricOrder label) ≤ _
  rw [metricOrder_metricDifferenceExpr]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

def principalExpr (e : Fin n → iota) (i j : Fin n) : Expr iota n :=
  Expr.sumFin (fun a => Expr.sumFin (fun b => principalTermExpr e a b i j))

def principalTopExpr (e : Fin n → iota) (i j : Fin n) (word : List iota) : Expr iota n :=
  Expr.sumFin (fun a => Expr.sumFin (fun b => principalTermTopExpr e a b i j word))

def principalTailExpr (e : Fin n → iota) (i j : Fin n) (word : List iota) : Expr iota n :=
  Expr.sumFin (fun a => Expr.sumFin (fun b => principalTermTailExpr e a b i j word))

theorem degree_principalTailExpr_le (e : Fin n → iota) (i j : Fin n) (word : List iota) :
    (principalTailExpr e i j word).degree ≤ word.length + 2 :=
  Expr.degree_sumFin_le _ _ (fun a => Expr.degree_sumFin_le _ _
    (fun b => degree_principalTermTailExpr_le e a b i j word))

theorem metricOrder_principalTailExpr_le (e : Fin n → iota)
    (i j : Fin n) (word : List iota) (label : Bool) :
    (principalTailExpr e i j word).metricOrder label ≤ word.length + 1 :=
  Expr.metricOrder_sumFin_le _ _ _ (fun a => Expr.metricOrder_sumFin_le _ _ _
    (fun b => metricOrder_principalTermTailExpr_le e a b i j word label))

theorem principalTail_highAtom_order (e : Fin n → iota) (i j : Fin n)
    (word : List iota) (r : ℕ) (hword : word.length ≤ 2 * r)
    (a : HighAtom (principalTailExpr e i j word) (r + 1)) :
    ∃ (label : Bool) (v : List iota) (k l : Fin n),
      a.val.val = Atom.metric label v k l ∧ r + 1 < v.length ∧ v.length ≤ 2 * r + 1 := by
  obtain ⟨label, v, k, l, ha, hlow, hhigh⟩ :=
    highAtom_is_metric (principalTailExpr e i j word) (r + 1) a
  refine ⟨label, v, k, l, ha, hlow, ?_⟩
  exact (hhigh.trans (metricOrder_principalTailExpr_le e i j word label)).trans (by omega)

def residualExpr (e : Fin n → iota) (i j : Fin n) : Expr iota n :=
  .add (principalExpr e i j) (lowerPerturbationExpr e i j)


def residualTraceExpr (e : Fin n → iota) (i j : Fin n) (word : List iota) : Expr iota n :=
  .add (principalTailExpr e i j word) ((lowerPerturbationExpr e i j).orderedDerivative word)

theorem degree_residualTraceExpr_le (e : Fin n → iota) (i j : Fin n) (word : List iota) :
    (residualTraceExpr e i j word).degree ≤ word.length + 2 := by
  change max (principalTailExpr e i j word).degree
    ((lowerPerturbationExpr e i j).orderedDerivative word).degree ≤ _
  exact max_le (degree_principalTailExpr_le e i j word)
    ((degree_ordered_lowerPerturbationExpr_le e i j word).trans (by omega))

theorem currentOrder_residualTraceExpr_le (e : Fin n → iota)
    (i j : Fin n) (word : List iota) :
    (residualTraceExpr e i j word).metricOrder false ≤ word.length + 1 := by
  change max ((principalTailExpr e i j word).metricOrder false)
    (((lowerPerturbationExpr e i j).orderedDerivative word).metricOrder false) ≤ _
  exact max_le (metricOrder_principalTailExpr_le e i j word false)
    ((currentOrder_ordered_lowerPerturbationExpr_le e i j word).trans (by omega))

private theorem orderedDerivative_add (word : List iota) (p q : Expr iota n) :
    (Expr.add p q).orderedDerivative word =
      Expr.add (p.orderedDerivative word) (q.orderedDerivative word) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    change Expr.derivative a ((Expr.add p q).orderedDerivative word) = _
    rw [ih]
    rfl

private theorem derivative_sumList {α : Type*} (a : iota)
    (l : List α) (f : α → Expr iota n) :
    (Expr.sumList l f).derivative a = Expr.sumList l (fun x => (f x).derivative a) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    change Expr.add ((f x).derivative a) ((Expr.sumList l f).derivative a) =
      Expr.add ((f x).derivative a) (Expr.sumList l (fun x => (f x).derivative a))
    rw [ih]

private theorem orderedDerivative_sumList {α : Type*} (word : List iota)
    (l : List α) (f : α → Expr iota n) :
    (Expr.sumList l f).orderedDerivative word =
      Expr.sumList l (fun x => (f x).orderedDerivative word) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
    rw [Expr.orderedDerivative, ih, derivative_sumList]
    rfl

private theorem orderedDerivative_sumFin (word : List iota) (f : Fin n → Expr iota n) :
    (Expr.sumFin f).orderedDerivative word =
      Expr.sumFin (fun a => (f a).orderedDerivative word) :=
  orderedDerivative_sumList word _ f

section Native

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (F : iota → SmoothField (n := n) (M := M))
  (G : Bool → M → Matrix (Fin n) (Fin n) ℝ)

theorem eval_inverseDifferenceExpr (a b : Fin n) (x : M) :
    (inverseDifferenceExpr a b).eval (nativeValues F G x) =
      (G false x)⁻¹ a b - (G true x)⁻¹ a b := by
  simp only [inverseDifferenceExpr, Expr.eval, nativeValues, sub_eq_add_neg]


theorem inverseDifferenceExpr_eq_zero (a b : Fin n) (x : M)
    (hG : G false x = G true x) :
    (inverseDifferenceExpr a b).eval (nativeValues F G x) = 0 := by
  rw [eval_inverseDifferenceExpr, hG, sub_self]

theorem principalTopExpr_eq_zero (e : Fin n → iota) (i j : Fin n) (word : List iota)
    (x : M) (hG : G false x = G true x) :
    (principalTopExpr e i j word).eval (nativeValues F G x) = 0 := by
  simp only [principalTopExpr, Expr.eval_sumFin]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  change (inverseDifferenceExpr a b).eval (nativeValues F G x) * _ = 0
  rw [inverseDifferenceExpr_eq_zero F G a b x hG, zero_mul]

variable (hG : ∀ b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
    (fun x i j => G b x i j)) (hdet : ∀ b x, (G b x).det ≠ 0)

include hG hdet

theorem metricDifferenceExpr_ordered_eval
    (headWord suffix : List iota) (i j : Fin n) (x : M) :
    (metricDifferenceExpr (headWord ++ suffix) i j).eval (nativeValues F G x) =
      directionalWord F headWord (fun y =>
        (metricDifferenceExpr suffix i j).eval (nativeValues F G y)) x := by
  rw [← orderedDerivative_metricDifferenceExpr]
  exact Expr.orderedDerivative_native _ F G hG hdet headWord x

theorem eval_metricDifferenceExpr (word : List iota) (i j : Fin n) (x : M) :
    (metricDifferenceExpr word i j).eval (nativeValues F G x) =
      directionalWord F word (fun y => G false y i j - G true y i j) x := by
  have h := metricDifferenceExpr_ordered_eval F G hG hdet word [] i j x
  simpa only [List.append_nil, metricDifferenceExpr, Expr.eval, nativeValues,
    directionalWord_nil, sub_eq_add_neg] using h


theorem ordered_principalTermExpr_split (e : Fin n → iota) (a b i j : Fin n)
    (word : List iota) (x : M) :
    ((principalTermExpr e a b i j).orderedDerivative word).eval (nativeValues F G x) =
      (principalTermTopExpr e a b i j word).eval (nativeValues F G x) +
        (principalTermTailExpr e a b i j word).eval (nativeValues F G x) := by
  rw [Expr.orderedDerivative_native _ F G hG hdet]
  change directionalWord F word (fun y =>
    (inverseDifferenceExpr a b).eval (nativeValues F G y) *
      (metricDifferenceExpr [e a, e b] i j).eval (nativeValues F G y)) x = _
  rw [directionalWord_mul_top_split F word
    ((inverseDifferenceExpr a b).native_contMDiff F G hG hdet)
    ((metricDifferenceExpr [e a, e b] i j).native_contMDiff F G hG hdet)]
  change _ = (inverseDifferenceExpr a b).eval (nativeValues F G x) *
    (metricDifferenceExpr (word ++ [e a, e b]) i j).eval (nativeValues F G x) + _
  rw [metricDifferenceExpr_ordered_eval F G hG hdet word [e a, e b] i j x]
  congr 1
  rw [principalTermTailExpr, Expr.eval_sumList]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [Expr.eval, Expr.orderedDerivative_native _ F G hG hdet,
    metricDifferenceExpr_ordered_eval F G hG hdet p.2 [e a, e b] i j x]

theorem ordered_principalExpr_split (e : Fin n → iota) (i j : Fin n)
    (word : List iota) (x : M) :
    ((principalExpr e i j).orderedDerivative word).eval (nativeValues F G x) =
      (principalTopExpr e i j word).eval (nativeValues F G x) +
        (principalTailExpr e i j word).eval (nativeValues F G x) := by
  simp only [principalExpr, orderedDerivative_sumFin, Expr.eval_sumFin,
    ordered_principalTermExpr_split F G hG hdet, principalTopExpr, principalTailExpr,
    Finset.sum_add_distrib]

theorem eval_principalTopExpr (e : Fin n → iota) (i j : Fin n)
    (word : List iota) (x : M) :
    (principalTopExpr e i j word).eval (nativeValues F G x) =
      ∑ a, ∑ b, ((G false x)⁻¹ a b - (G true x)⁻¹ a b) *
        directionalWord F (word ++ [e a, e b])
          (fun y => G false y i j - G true y i j) x := by
  simp only [principalTopExpr, Expr.eval_sumFin]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (inverseDifferenceExpr a b).eval (nativeValues F G x) *
    (metricDifferenceExpr (word ++ [e a, e b]) i j).eval (nativeValues F G x) = _
  rw [eval_inverseDifferenceExpr F G, eval_metricDifferenceExpr F G hG hdet]


theorem ordered_residualExpr_split (e : Fin n → iota) (i j : Fin n)
    (word : List iota) (x : M) :
    ((residualExpr e i j).orderedDerivative word).eval (nativeValues F G x) =
      (principalTopExpr e i j word).eval (nativeValues F G x) +
        (residualTraceExpr e i j word).eval (nativeValues F G x) := by
  simp only [residualExpr, orderedDerivative_add, Expr.eval,
    ordered_principalExpr_split F G hG hdet, residualTraceExpr]
  ring

end Native

section Compatible

open DeTurckNative DeTurckCompatibleJetNative DeTurckJetCoordinatesNative

variable {M : Type v} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] {a : M} {K : Set M}
  (F : iota → SmoothField (n := n) (M := M)) (C : Cutoffs (n := n) a K)
  (g0 g : RiemannianMetric n M)

theorem eval_principalExpr_compatible (i j : Fin n) (x : M) :
    (principalExpr Sum.inl i j).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      lowerJetContraction ((C.matrix g x)⁻¹ - (C.matrix g0 x)⁻¹)
        (C.secondDifference g0 g x) i j := by
  simp only [principalExpr, Expr.eval_sumFin, principalTermExpr, inverseDifferenceExpr,
    metricDifferenceExpr, Expr.eval, nativeValues, compatibleMatrix]
  change (∑ k, ∑ l, ((C.matrix g x)⁻¹ k l + -(C.matrix g0 x)⁻¹ k l) *
    ((C.jet g x).second k l i j + -(C.jet g0 x).second k l i j)) = _
  simp only [lowerJetContraction, Cutoffs.secondDifference, Matrix.sub_apply,
    Pi.sub_apply, sub_eq_add_neg]


theorem eval_residualExpr_compatible (i j : Fin n) (x : M) :
    (residualExpr Sum.inl i j).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      C.residual g0 g x i j := by
  rw [residualExpr, Expr.eval, eval_principalExpr_compatible,
    eval_lowerPerturbationExpr_compatible]
  have hp : backgroundLowerJet (C.jet g0 x) + C.lowerDifference g0 g x =
      backgroundLowerJet (C.jet g x) := by
    dsimp only [Cutoffs.lowerDifference]
    abel
  have hq : (C.jet g0 x).second + C.secondDifference g0 g x = (C.jet g x).second := by
    dsimp only [Cutoffs.secondDifference]
    abel
  have hvalue : (C.jet g0 x).value + (C.lowerDifference g0 g x).1 = (C.jet g x).value :=
    congrArg Prod.fst hp
  have hsplit := DeTurckMetricProducerNative.perturbationRemainder_split (C.jet g0 x)
    (C.lowerDifference g0 g x) (C.secondDifference g0 g x)
    (by rw [hvalue]; exact C.matrix_posDef g x)
    (by rw [hq]; exact C.jet_second_symm g x)
    (by rw [hq]; exact C.jet_second_swap g x)
  rw [hvalue, hp] at hsplit
  exact (congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hsplit).symm

theorem eval_residualExpr_source_compatible (i j : Fin n) (x : M) :
    (residualExpr Sum.inl i j).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      ricciDeTurckSource (C.jet g0 x) (C.jet g x) i j -
        lowerJetContraction (C.matrix g0 x)⁻¹
          ((C.jet g x).second - (C.jet g0 x).second) i j :=
  (eval_residualExpr_compatible F C g0 g i j x).trans (C.residual_eq_source g0 g x i j)

theorem ordered_residualExpr_compatible (i j : Fin n) (word : List iota) (x : M) :
    ((residualExpr Sum.inl i j).orderedDerivative (word.map Sum.inr)).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      directionalWord F word (fun y => C.residual g0 g y i j) x := by
  rw [Expr.orderedDerivative_native _ (combinedFields F C) (compatibleMatrix C g0 g)
    (compatibleMatrix_contMDiff C g0 g) (compatibleMatrix_det_ne_zero C g0 g)]
  have heq : (fun y => (residualExpr Sum.inl i j).eval
      (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) y)) =
        fun y => C.residual g0 g y i j :=
    funext (eval_residualExpr_compatible F C g0 g i j)
  rw [heq, directionalWord_combined_inr]


theorem residual_top_trace_compatible (i j : Fin n) (word : List iota) (x : M) :
    directionalWord F word (fun y => C.residual g0 g y i j) x =
      (principalTopExpr Sum.inl i j (word.map Sum.inr)).eval
          (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) +
        (residualTraceExpr Sum.inl i j (word.map Sum.inr)).eval
          (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) := by
  letI : MeasurableSpace M := borel M
  letI : BorelSpace M := ⟨rfl⟩
  rw [← ordered_residualExpr_compatible F C g0 g i j word x]
  exact ordered_residualExpr_split (combinedFields F C) (compatibleMatrix C g0 g)
    (compatibleMatrix_contMDiff C g0 g) (compatibleMatrix_det_ne_zero C g0 g)
    Sum.inl i j (word.map Sum.inr) x

end Compatible

end PoincareConjecture.DeTurckPrincipalForcingNative

end

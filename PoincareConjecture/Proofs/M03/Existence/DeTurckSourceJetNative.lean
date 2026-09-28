import PoincareConjecture.Proofs.M03.Existence.DeTurckRationalJetNative
import PoincareConjecture.Proofs.M03.Existence.DeTurckJetCoordinatesNative

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.DeTurckSourceJetNative

open DeTurckNative DeTurckRationalJetNative TensorProbeNative

universe u v

variable {iota : Type u} {n : ℕ}

private def subExpr (p q : Expr iota n) : Expr iota n := .add p (.neg q)

def valueExpr (b : Bool) (i j : Fin n) : Expr iota n :=
  .atom (.metric b [] i j)

def inverseExpr (b : Bool) (i j : Fin n) : Expr iota n :=
  .atom (.inverse b i j)

def firstExpr (e : Fin n → iota) (b : Bool) (a i j : Fin n) : Expr iota n :=
  .atom (.metric b [e a] i j)

def secondExpr (e : Fin n → iota) (eraseCurrent b : Bool)
    (a c i j : Fin n) : Expr iota n :=
  if eraseCurrent && !b then .constant 0 else .atom (.metric b [e a, e c] i j)

def christoffelExpr (e : Fin n → iota) (b : Bool) (k i j : Fin n) : Expr iota n :=
  .mul (.constant (1 / 2)) (Expr.sumFin (fun l =>
    .mul (inverseExpr b k l)
      (subExpr (.add (firstExpr e b i l j) (firstExpr e b j l i))
        (firstExpr e b l i j))))

def inverseFirstExpr (e : Fin n → iota) (b : Bool) (a k l : Fin n) : Expr iota n :=
  .neg (Expr.sumFin (fun s => Expr.sumFin (fun t =>
    .mul (.mul (inverseExpr b k s) (firstExpr e b a s t)) (inverseExpr b t l))))

def christoffelSecondExpr (e : Fin n → iota) (eraseCurrent b : Bool)
    (a k i j : Fin n) : Expr iota n :=
  .mul (.constant (1 / 2)) (Expr.sumFin (fun l =>
    .add
      (.mul (inverseFirstExpr e b a k l)
        (subExpr (.add (firstExpr e b i l j) (firstExpr e b j l i))
          (firstExpr e b l i j)))
      (.mul (inverseExpr b k l)
        (subExpr (.add (secondExpr e eraseCurrent b a i l j)
          (secondExpr e eraseCurrent b a j l i))
          (secondExpr e eraseCurrent b a l i j)))))

def curvatureExpr (e : Fin n → iota) (eraseCurrent b : Bool)
    (i j k l : Fin n) : Expr iota n :=
  .add (subExpr (christoffelSecondExpr e eraseCurrent b i l j k)
    (christoffelSecondExpr e eraseCurrent b j l i k))
    (Expr.sumFin (fun m => subExpr
      (.mul (christoffelExpr e b m j k) (christoffelExpr e b l i m))
      (.mul (christoffelExpr e b m i k) (christoffelExpr e b l j m))))

def ricciExpr (e : Fin n → iota) (eraseCurrent b : Bool)
    (i j : Fin n) : Expr iota n :=
  Expr.sumFin (fun k => curvatureExpr e eraseCurrent b k i j k)

def vectorExpr (e : Fin n → iota) (k : Fin n) : Expr iota n :=
  Expr.sumFin (fun a => Expr.sumFin (fun b =>
    .mul (inverseExpr false a b)
      (subExpr (christoffelExpr e false k a b) (christoffelExpr e true k a b))))

def vectorFirstExpr (e : Fin n → iota) (eraseCurrent : Bool)
    (a k : Fin n) : Expr iota n :=
  Expr.sumFin (fun s => Expr.sumFin (fun t =>
    .add
      (.mul (inverseFirstExpr e false a s t)
        (subExpr (christoffelExpr e false k s t) (christoffelExpr e true k s t)))
      (.mul (inverseExpr false s t)
        (subExpr (christoffelSecondExpr e eraseCurrent false a k s t)
          (christoffelSecondExpr e eraseCurrent true a k s t)))))

def lieExpr (e : Fin n → iota) (eraseCurrent : Bool) (i j : Fin n) : Expr iota n :=
  Expr.sumFin (fun k => .add
    (.add (.mul (vectorExpr e k) (firstExpr e false k i j))
      (.mul (valueExpr false k j) (vectorFirstExpr e eraseCurrent i k)))
    (.mul (valueExpr false i k) (vectorFirstExpr e eraseCurrent j k)))

def sourceExpr (e : Fin n → iota) (eraseCurrent : Bool) (i j : Fin n) : Expr iota n :=
  .add (.mul (.constant (-2)) (ricciExpr e eraseCurrent false i j))
    (lieExpr e eraseCurrent i j)

def backgroundContractionExpr (e : Fin n → iota) (i j : Fin n) : Expr iota n :=
  Expr.sumFin (fun a => Expr.sumFin (fun b =>
    .mul (inverseExpr false a b) (secondExpr e false true a b i j)))

def lowerPerturbationExpr (e : Fin n → iota) (i j : Fin n) : Expr iota n :=
  .add (backgroundContractionExpr e i j) (sourceExpr e true i j)

section Evaluation

variable {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [Fintype iota]
  (F : iota → SmoothField (n := n) (M := M))
  (G : Bool → M → Matrix (Fin n) (Fin n) ℝ) (e : Fin n → iota)

def nativeJet (eraseCurrent b : Bool) (x : M) : MetricJet2 (n := n) where
  value := G b x
  first a i j := directionalWord F [e a] (fun y => G b y i j) x
  second a c i j := if eraseCurrent && !b then 0 else
    directionalWord F [e a, e c] (fun y => G b y i j) x

@[simp] theorem nativeJet_background (eraseCurrent : Bool) (x : M) :
    nativeJet F G e eraseCurrent true x = nativeJet F G e false true x := by
  cases eraseCurrent <;> rfl

@[simp] theorem nativeJet_erase_current (x : M) :
    nativeJet F G e true false x = eraseSecondJet (nativeJet F G e false false x) := rfl

theorem eval_christoffelExpr (eraseCurrent b : Bool) (k i j : Fin n) (x : M) :
    (christoffelExpr e b k i j).eval (nativeValues F G x) =
      christoffelJet (nativeJet F G e eraseCurrent b x) k i j := by
  simp only [christoffelExpr, subExpr, inverseExpr, firstExpr, Expr.eval, Expr.eval_sumFin,
    nativeValues, nativeJet, christoffelJet, sub_eq_add_neg]

theorem eval_inverseFirstExpr (eraseCurrent b : Bool) (a k l : Fin n) (x : M) :
    (inverseFirstExpr e b a k l).eval (nativeValues F G x) =
      inverseFirst (nativeJet F G e eraseCurrent b x) a k l := by
  simp only [inverseFirstExpr, inverseExpr, firstExpr, Expr.eval, Expr.eval_sumFin,
    nativeValues, nativeJet, inverseFirst]

theorem eval_secondExpr (eraseCurrent b : Bool) (a c i j : Fin n) (x : M) :
    (secondExpr e eraseCurrent b a c i j).eval (nativeValues F G x) =
      (nativeJet F G e eraseCurrent b x).second a c i j := by
  cases eraseCurrent <;> cases b <;> rfl

theorem eval_christoffelSecondExpr (eraseCurrent b : Bool)
    (a k i j : Fin n) (x : M) :
    (christoffelSecondExpr e eraseCurrent b a k i j).eval (nativeValues F G x) =
      christoffelSecond (nativeJet F G e eraseCurrent b x) a k i j := by
  simp only [christoffelSecondExpr, subExpr, Expr.eval, Expr.eval_sumFin,
    eval_inverseFirstExpr F G e eraseCurrent, eval_secondExpr F G e eraseCurrent,
    inverseExpr, firstExpr, nativeValues, nativeJet, christoffelSecond, sub_eq_add_neg]

theorem eval_curvatureExpr (eraseCurrent b : Bool) (i j k l : Fin n) (x : M) :
    (curvatureExpr e eraseCurrent b i j k l).eval (nativeValues F G x) =
      mixedCurvatureJet (nativeJet F G e eraseCurrent b x) i j k l := by
  simp only [curvatureExpr, subExpr, Expr.eval, Expr.eval_sumFin,
    eval_christoffelSecondExpr F G e eraseCurrent,
    eval_christoffelExpr F G e eraseCurrent, mixedCurvatureJet, sub_eq_add_neg]

theorem eval_ricciExpr (eraseCurrent b : Bool) (i j : Fin n) (x : M) :
    (ricciExpr e eraseCurrent b i j).eval (nativeValues F G x) =
      ricciJet (nativeJet F G e eraseCurrent b x) i j := by
  simp only [ricciExpr, Expr.eval_sumFin, eval_curvatureExpr F G e eraseCurrent, ricciJet]

theorem eval_vectorExpr (eraseCurrent : Bool) (k : Fin n) (x : M) :
    (vectorExpr e k).eval (nativeValues F G x) =
      deTurckVector (nativeJet F G e eraseCurrent true x)
        (nativeJet F G e eraseCurrent false x) k := by
  simp only [vectorExpr, subExpr, Expr.eval_sumFin, Expr.eval,
    eval_christoffelExpr F G e eraseCurrent, inverseExpr, nativeValues,
    nativeJet, deTurckVector, sub_eq_add_neg]

theorem eval_vectorFirstExpr (eraseCurrent : Bool) (a k : Fin n) (x : M) :
    (vectorFirstExpr e eraseCurrent a k).eval (nativeValues F G x) =
      deTurckVectorFirst (nativeJet F G e eraseCurrent true x)
        (nativeJet F G e eraseCurrent false x) a k := by
  simp only [vectorFirstExpr, subExpr, Expr.eval_sumFin, Expr.eval,
    eval_inverseFirstExpr F G e eraseCurrent, eval_christoffelExpr F G e eraseCurrent,
    eval_christoffelSecondExpr F G e eraseCurrent, inverseExpr, nativeValues,
    nativeJet, deTurckVectorFirst, sub_eq_add_neg]

theorem eval_lieExpr (eraseCurrent : Bool) (i j : Fin n) (x : M) :
    (lieExpr e eraseCurrent i j).eval (nativeValues F G x) =
      lieDerivativeJet (nativeJet F G e eraseCurrent true x)
        (nativeJet F G e eraseCurrent false x) i j := by
  simp only [lieExpr, Expr.eval_sumFin, Expr.eval, eval_vectorExpr F G e eraseCurrent,
    eval_vectorFirstExpr F G e eraseCurrent, valueExpr, firstExpr, nativeValues,
    directionalWord_nil, nativeJet, lieDerivativeJet]

theorem eval_sourceExpr (eraseCurrent : Bool) (i j : Fin n) (x : M) :
    (sourceExpr e eraseCurrent i j).eval (nativeValues F G x) =
      ricciDeTurckSource (nativeJet F G e false true x)
        (nativeJet F G e eraseCurrent false x) i j := by
  simp only [sourceExpr, Expr.eval, eval_ricciExpr F G e eraseCurrent,
    eval_lieExpr F G e eraseCurrent, nativeJet_background, ricciDeTurckSource]

theorem eval_lower_sourceExpr (i j : Fin n) (x : M) :
    (sourceExpr e true i j).eval (nativeValues F G x) =
      ricciDeTurckSource (nativeJet F G e false true x)
        (eraseSecondJet (nativeJet F G e false false x)) i j := by
  rw [eval_sourceExpr, nativeJet_erase_current]

theorem eval_backgroundContractionExpr (i j : Fin n) (x : M) :
    (backgroundContractionExpr e i j).eval (nativeValues F G x) =
      secondJetSource (G false x) (nativeJet F G e false true x).second i j := by
  simp only [backgroundContractionExpr, Expr.eval_sumFin, Expr.eval,
    inverseExpr, nativeValues, eval_secondExpr F G e false, secondJetSource]

theorem eval_lowerPerturbationExpr (i j : Fin n) (x : M) :
    (lowerPerturbationExpr e i j).eval (nativeValues F G x) =
      secondJetSource (G false x) (nativeJet F G e false true x).second i j +
        ricciDeTurckSource (nativeJet F G e false true x)
          (eraseSecondJet (nativeJet F G e false false x)) i j := by
  rw [lowerPerturbationExpr, Expr.eval, eval_backgroundContractionExpr, eval_lower_sourceExpr]

theorem ordered_sourceExpr_native
    (hG : ∀ b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => G b x i j))
    (hdet : ∀ b x, (G b x).det ≠ 0) (eraseCurrent : Bool)
    (i j : Fin n) (w : List iota) (x : M) :
    ((sourceExpr e eraseCurrent i j).orderedDerivative w).eval (nativeValues F G x) =
      directionalWord F w (fun y => ricciDeTurckSource (nativeJet F G e false true y)
        (nativeJet F G e eraseCurrent false y) i j) x := by
  rw [Expr.orderedDerivative_native _ F G hG hdet]
  exact congrArg (fun f : M → ℝ => directionalWord F w f x)
    (funext (eval_sourceExpr F G e eraseCurrent i j))

theorem ordered_lowerPerturbationExpr_native
    (hG : ∀ b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => G b x i j))
    (hdet : ∀ b x, (G b x).det ≠ 0)
    (i j : Fin n) (w : List iota) (x : M) :
    ((lowerPerturbationExpr e i j).orderedDerivative w).eval (nativeValues F G x) =
      directionalWord F w (fun y =>
        secondJetSource (G false y) (nativeJet F G e false true y).second i j +
          ricciDeTurckSource (nativeJet F G e false true y)
            (eraseSecondJet (nativeJet F G e false false y)) i j) x := by
  rw [Expr.orderedDerivative_native _ F G hG hdet]
  exact congrArg (fun f : M → ℝ => directionalWord F w f x)
    (funext (eval_lowerPerturbationExpr F G e i j))

end Evaluation

section Degree

variable (e : Fin n → iota)

private theorem degree_add_le {p q : Expr iota n} {k : ℕ}
    (hp : p.degree ≤ k) (hq : q.degree ≤ k) : (Expr.add p q).degree ≤ k :=
  max_le hp hq

private theorem degree_sub_le {p q : Expr iota n} {k : ℕ}
    (hp : p.degree ≤ k) (hq : q.degree ≤ k) : (subExpr p q).degree ≤ k :=
  max_le hp hq

private theorem degree_mul_le {p q : Expr iota n} {a b : ℕ}
    (hp : p.degree ≤ a) (hq : q.degree ≤ b) : (Expr.mul p q).degree ≤ a + b :=
  Nat.add_le_add hp hq

theorem degree_secondExpr_le (eraseCurrent b : Bool) (a c i j : Fin n) :
    (secondExpr e eraseCurrent b a c i j).degree ≤ 2 := by
  cases eraseCurrent <;> cases b <;> simp [secondExpr, Expr.degree, Atom.weight]

theorem degree_christoffelExpr_le (b : Bool) (k i j : Fin n) :
    (christoffelExpr e b k i j).degree ≤ 1 := by
  simp only [christoffelExpr, Expr.degree, Nat.zero_add]
  apply Expr.degree_sumFin_le
  intro l
  simp [inverseExpr, firstExpr, subExpr, Expr.degree, Atom.weight]

theorem degree_inverseFirstExpr_le (b : Bool) (a k l : Fin n) :
    (inverseFirstExpr e b a k l).degree ≤ 1 := by
  apply Expr.degree_sumFin_le
  intro s
  apply Expr.degree_sumFin_le
  intro t
  simp [inverseExpr, firstExpr, Expr.degree, Atom.weight]

theorem degree_christoffelSecondExpr_le (eraseCurrent b : Bool) (a k i j : Fin n) :
    (christoffelSecondExpr e eraseCurrent b a k i j).degree ≤ 2 := by
  simp only [christoffelSecondExpr, Expr.degree, Nat.zero_add]
  apply Expr.degree_sumFin_le
  intro l
  apply degree_add_le
  · exact degree_mul_le (degree_inverseFirstExpr_le e b a k l)
      (show (subExpr (.add (firstExpr e b i l j) (firstExpr e b j l i))
        (firstExpr e b l i j)).degree ≤ 1 by
        simp [firstExpr, subExpr, Expr.degree, Atom.weight])
  · exact degree_mul_le (show (inverseExpr b k l : Expr iota n).degree ≤ 0 from le_rfl)
      (degree_sub_le (degree_add_le (degree_secondExpr_le e eraseCurrent b a i l j)
        (degree_secondExpr_le e eraseCurrent b a j l i))
        (degree_secondExpr_le e eraseCurrent b a l i j))

theorem degree_curvatureExpr_le (eraseCurrent b : Bool) (i j k l : Fin n) :
    (curvatureExpr e eraseCurrent b i j k l).degree ≤ 2 := by
  apply degree_add_le
  · exact degree_sub_le (degree_christoffelSecondExpr_le e eraseCurrent b i l j k)
      (degree_christoffelSecondExpr_le e eraseCurrent b j l i k)
  · apply Expr.degree_sumFin_le
    intro m
    exact degree_sub_le
      (degree_mul_le (degree_christoffelExpr_le e b m j k) (degree_christoffelExpr_le e b l i m))
      (degree_mul_le (degree_christoffelExpr_le e b m i k) (degree_christoffelExpr_le e b l j m))

theorem degree_ricciExpr_le (eraseCurrent b : Bool) (i j : Fin n) :
    (ricciExpr e eraseCurrent b i j).degree ≤ 2 :=
  Expr.degree_sumFin_le _ _ (fun k => degree_curvatureExpr_le e eraseCurrent b k i j k)

theorem degree_vectorExpr_le (k : Fin n) : (vectorExpr e k).degree ≤ 1 := by
  apply Expr.degree_sumFin_le
  intro a
  apply Expr.degree_sumFin_le
  intro b
  exact degree_mul_le (show (inverseExpr false a b : Expr iota n).degree ≤ 0 from le_rfl)
    (degree_sub_le (degree_christoffelExpr_le e false k a b)
      (degree_christoffelExpr_le e true k a b))

theorem degree_vectorFirstExpr_le (eraseCurrent : Bool) (a k : Fin n) :
    (vectorFirstExpr e eraseCurrent a k).degree ≤ 2 := by
  apply Expr.degree_sumFin_le
  intro s
  apply Expr.degree_sumFin_le
  intro t
  apply degree_add_le
  · exact degree_mul_le (degree_inverseFirstExpr_le e false a s t)
      (degree_sub_le (degree_christoffelExpr_le e false k s t)
        (degree_christoffelExpr_le e true k s t))
  · exact degree_mul_le (show (inverseExpr false s t : Expr iota n).degree ≤ 0 from le_rfl)
      (degree_sub_le (degree_christoffelSecondExpr_le e eraseCurrent false a k s t)
        (degree_christoffelSecondExpr_le e eraseCurrent true a k s t))

theorem degree_lieExpr_le (eraseCurrent : Bool) (i j : Fin n) :
    (lieExpr e eraseCurrent i j).degree ≤ 2 := by
  apply Expr.degree_sumFin_le
  intro k
  apply degree_add_le
  · apply degree_add_le
    · exact degree_mul_le (degree_vectorExpr_le e k)
        (show (firstExpr e false k i j).degree ≤ 1 from le_rfl)
    · exact degree_mul_le (show (valueExpr false k j : Expr iota n).degree ≤ 0 from le_rfl)
        (degree_vectorFirstExpr_le e eraseCurrent i k)
  · exact degree_mul_le (show (valueExpr false i k : Expr iota n).degree ≤ 0 from le_rfl)
      (degree_vectorFirstExpr_le e eraseCurrent j k)

theorem degree_sourceExpr_le (eraseCurrent : Bool) (i j : Fin n) :
    (sourceExpr e eraseCurrent i j).degree ≤ 2 :=
  degree_add_le
    (degree_mul_le (show (Expr.constant (-2) : Expr iota n).degree ≤ 0 from le_rfl)
      (degree_ricciExpr_le e eraseCurrent false i j))
    (degree_lieExpr_le e eraseCurrent i j)

theorem degree_ordered_sourceExpr_le (eraseCurrent : Bool) (i j : Fin n) (w : List iota) :
    ((sourceExpr e eraseCurrent i j).orderedDerivative w).degree ≤ 2 + w.length :=
  (Expr.degree_orderedDerivative_le w _).trans
    (Nat.add_le_add_right (degree_sourceExpr_le e eraseCurrent i j) w.length)

theorem degree_backgroundContractionExpr_le (i j : Fin n) :
    (backgroundContractionExpr e i j).degree ≤ 2 := by
  apply Expr.degree_sumFin_le
  intro a
  apply Expr.degree_sumFin_le
  intro b
  exact degree_mul_le (show (inverseExpr false a b : Expr iota n).degree ≤ 0 from le_rfl)
    (degree_secondExpr_le e false true a b i j)

theorem degree_lowerPerturbationExpr_le (i j : Fin n) :
    (lowerPerturbationExpr e i j).degree ≤ 2 :=
  degree_add_le (degree_backgroundContractionExpr_le e i j) (degree_sourceExpr_le e true i j)

theorem degree_ordered_lowerPerturbationExpr_le (i j : Fin n) (w : List iota) :
    ((lowerPerturbationExpr e i j).orderedDerivative w).degree ≤ 2 + w.length :=
  (Expr.degree_orderedDerivative_le w _).trans
    (Nat.add_le_add_right (degree_lowerPerturbationExpr_le e i j) w.length)

end Degree

section CurrentOrder

private theorem metricOrder_le_degree (p : Expr iota n) (b : Bool) :
    p.metricOrder b ≤ p.degree := by
  induction p with
  | constant c => exact le_rfl
  | atom a =>
    cases a with
    | metric c w i j =>
      by_cases h : c = b <;> simp [Expr.metricOrder, Expr.degree, Atom.weight, h]
    | inverse c i j => exact le_rfl
  | add p q hp hq => exact max_le_max hp hq
  | mul p q hp hq =>
    change max (p.metricOrder b) (q.metricOrder b) ≤ p.degree + q.degree
    omega
  | neg p hp => exact hp

private theorem current_add_le {p q : Expr iota n} {k : ℕ}
    (hp : p.metricOrder false ≤ k) (hq : q.metricOrder false ≤ k) :
    (Expr.add p q).metricOrder false ≤ k := max_le hp hq

private theorem current_sub_le {p q : Expr iota n} {k : ℕ}
    (hp : p.metricOrder false ≤ k) (hq : q.metricOrder false ≤ k) :
    (subExpr p q).metricOrder false ≤ k := max_le hp hq

private theorem current_mul_le {p q : Expr iota n} {k : ℕ}
    (hp : p.metricOrder false ≤ k) (hq : q.metricOrder false ≤ k) :
    (Expr.mul p q).metricOrder false ≤ k := max_le hp hq

variable (e : Fin n → iota)

theorem currentOrder_secondExpr_lower (b : Bool) (a c i j : Fin n) :
    (secondExpr e true b a c i j).metricOrder false = 0 := by
  cases b <;> simp [secondExpr, Expr.metricOrder]

theorem currentOrder_christoffelSecondExpr_lower (b : Bool) (a k i j : Fin n) :
    (christoffelSecondExpr e true b a k i j).metricOrder false ≤ 1 := by
  apply current_mul_le (show (Expr.constant (1 / 2) : Expr iota n).metricOrder false ≤ 1 by
    simp [Expr.metricOrder])
  apply Expr.metricOrder_sumFin_le
  intro l
  apply current_add_le
  · apply current_mul_le
    · exact (metricOrder_le_degree _ false).trans (degree_inverseFirstExpr_le e b a k l)
    · exact (metricOrder_le_degree _ false).trans
        (show (subExpr (.add (firstExpr e b i l j) (firstExpr e b j l i))
          (firstExpr e b l i j)).degree ≤ 1 by
          simp [firstExpr, subExpr, Expr.degree, Atom.weight])
  · apply current_mul_le
    · simp [inverseExpr, Expr.metricOrder]
    · apply current_sub_le
      · apply current_add_le <;> rw [currentOrder_secondExpr_lower] <;> omega
      · rw [currentOrder_secondExpr_lower]
        omega

theorem currentOrder_curvatureExpr_lower (b : Bool) (i j k l : Fin n) :
    (curvatureExpr e true b i j k l).metricOrder false ≤ 1 := by
  apply current_add_le
  · exact current_sub_le (currentOrder_christoffelSecondExpr_lower e b i l j k)
      (currentOrder_christoffelSecondExpr_lower e b j l i k)
  · apply Expr.metricOrder_sumFin_le
    intro m
    apply current_sub_le
    · exact current_mul_le
        ((metricOrder_le_degree _ false).trans (degree_christoffelExpr_le e b m j k))
        ((metricOrder_le_degree _ false).trans (degree_christoffelExpr_le e b l i m))
    · exact current_mul_le
        ((metricOrder_le_degree _ false).trans (degree_christoffelExpr_le e b m i k))
        ((metricOrder_le_degree _ false).trans (degree_christoffelExpr_le e b l j m))

theorem currentOrder_ricciExpr_lower (i j : Fin n) :
    (ricciExpr e true false i j).metricOrder false ≤ 1 :=
  Expr.metricOrder_sumFin_le _ _ _ (fun k => currentOrder_curvatureExpr_lower e false k i j k)

theorem currentOrder_vectorFirstExpr_lower (a k : Fin n) :
    (vectorFirstExpr e true a k).metricOrder false ≤ 1 := by
  apply Expr.metricOrder_sumFin_le
  intro s
  apply Expr.metricOrder_sumFin_le
  intro t
  apply current_add_le
  · apply current_mul_le
    · exact (metricOrder_le_degree _ false).trans (degree_inverseFirstExpr_le e false a s t)
    · exact current_sub_le
        ((metricOrder_le_degree _ false).trans (degree_christoffelExpr_le e false k s t))
        ((metricOrder_le_degree _ false).trans (degree_christoffelExpr_le e true k s t))
  · apply current_mul_le
    · simp [inverseExpr, Expr.metricOrder]
    · exact current_sub_le (currentOrder_christoffelSecondExpr_lower e false a k s t)
        (currentOrder_christoffelSecondExpr_lower e true a k s t)

theorem currentOrder_lieExpr_lower (i j : Fin n) :
    (lieExpr e true i j).metricOrder false ≤ 1 := by
  apply Expr.metricOrder_sumFin_le
  intro k
  apply current_add_le
  · apply current_add_le
    · exact current_mul_le
        ((metricOrder_le_degree _ false).trans (degree_vectorExpr_le e k))
        (show (firstExpr e false k i j).metricOrder false ≤ 1 by
          simp [firstExpr, Expr.metricOrder])
    · exact current_mul_le
        (show (valueExpr false k j : Expr iota n).metricOrder false ≤ 1 by
          simp [valueExpr, Expr.metricOrder]) (currentOrder_vectorFirstExpr_lower e i k)
  · exact current_mul_le
      (show (valueExpr false i k : Expr iota n).metricOrder false ≤ 1 by
        simp [valueExpr, Expr.metricOrder]) (currentOrder_vectorFirstExpr_lower e j k)

theorem currentOrder_sourceExpr_lower (i j : Fin n) :
    (sourceExpr e true i j).metricOrder false ≤ 1 :=
  current_add_le
    (current_mul_le
      (show (Expr.constant (-2) : Expr iota n).metricOrder false ≤ 1 by
        simp [Expr.metricOrder]) (currentOrder_ricciExpr_lower e i j))
    (currentOrder_lieExpr_lower e i j)

theorem currentOrder_sourceExpr_full (i j : Fin n) :
    (sourceExpr e false i j).metricOrder false ≤ 2 :=
  (metricOrder_le_degree _ false).trans (degree_sourceExpr_le e false i j)

theorem currentOrder_ordered_sourceExpr_lower (i j : Fin n) (w : List iota) :
    ((sourceExpr e true i j).orderedDerivative w).metricOrder false ≤ 1 + w.length :=
  (Expr.metricOrder_orderedDerivative_le w _ false).trans
    (Nat.add_le_add_right (currentOrder_sourceExpr_lower e i j) w.length)

theorem currentOrder_ordered_sourceExpr_full (i j : Fin n) (w : List iota) :
    ((sourceExpr e false i j).orderedDerivative w).metricOrder false ≤ 2 + w.length :=
  (Expr.metricOrder_orderedDerivative_le w _ false).trans
    (Nat.add_le_add_right (currentOrder_sourceExpr_full e i j) w.length)

theorem currentOrder_backgroundContractionExpr (i j : Fin n) :
    (backgroundContractionExpr e i j).metricOrder false = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Expr.metricOrder_sumFin_le
  intro a
  apply Expr.metricOrder_sumFin_le
  intro b
  simp [inverseExpr, secondExpr, Expr.metricOrder]

theorem currentOrder_lowerPerturbationExpr_le (i j : Fin n) :
    (lowerPerturbationExpr e i j).metricOrder false ≤ 1 :=
  current_add_le (by rw [currentOrder_backgroundContractionExpr]; omega)
    (currentOrder_sourceExpr_lower e i j)

theorem currentOrder_ordered_lowerPerturbationExpr_le (i j : Fin n) (w : List iota) :
    ((lowerPerturbationExpr e i j).orderedDerivative w).metricOrder false ≤ 1 + w.length :=
  (Expr.metricOrder_orderedDerivative_le w _ false).trans
    (Nat.add_le_add_right (currentOrder_lowerPerturbationExpr_le e i j) w.length)

end CurrentOrder

section Compatible

open DeTurckCompatibleJetNative DeTurckJetCoordinatesNative

variable {M : Type v} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [Fintype iota] {p : M} {K : Set M}
  (F : iota → SmoothField (n := n) (M := M)) (C : Cutoffs (n := n) p K)
  (g0 g : RiemannianMetric n M)

def compatibleMatrix : Bool → M → Matrix (Fin n) (Fin n) ℝ
  | true => C.matrix g0
  | false => C.matrix g

theorem compatibleMatrix_contMDiff (b : Bool) :
    ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => compatibleMatrix C g0 g b x i j) := by
  cases b with
  | false => exact C.matrix_contMDiff g
  | true => exact C.matrix_contMDiff g0

theorem compatibleMatrix_det_ne_zero (b : Bool) (x : M) :
    (compatibleMatrix C g0 g b x).det ≠ 0 := by
  cases b with
  | false =>
    exact ((C.matrix g x).isUnit_iff_isUnit_det.mp (C.matrix_posDef g x).isUnit).ne_zero
  | true =>
    exact ((C.matrix g0 x).isUnit_iff_isUnit_det.mp (C.matrix_posDef g0 x).isUnit).ne_zero

theorem nativeJet_compatible_background (x : M) :
    nativeJet (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl false true x =
      C.jet g0 x := rfl

theorem nativeJet_compatible_current (x : M) :
    nativeJet (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl false false x =
      C.jet g x := rfl

theorem directionalWord_combined_inr (w : List iota) (f : M → ℝ) :
    directionalWord (combinedFields F C) (w.map Sum.inr) f = directionalWord F w f := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change scalarDirectional (F a)
        (directionalWord (combinedFields F C) (w.map Sum.inr) f) =
      scalarDirectional (F a) (directionalWord F w f)
    rw [ih]

theorem eval_sourceExpr_compatible (i j : Fin n) (x : M) :
    (sourceExpr Sum.inl false i j).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      ricciDeTurckSource (C.jet g0 x) (C.jet g x) i j := by
  simpa only [nativeJet_compatible_background, nativeJet_compatible_current] using
    eval_sourceExpr (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl false i j x

theorem eval_lower_sourceExpr_compatible (i j : Fin n) (x : M) :
    (sourceExpr Sum.inl true i j).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      lowerJetSource (C.jet g0 x) (backgroundLowerJet (C.jet g x)) i j := by
  change _ = ricciDeTurckSource (C.jet g0 x) (eraseSecondJet (C.jet g x)) i j
  simpa only [nativeJet_compatible_background, nativeJet_compatible_current] using
    eval_lower_sourceExpr (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl i j x

theorem eval_backgroundContractionExpr_compatible (i j : Fin n) (x : M) :
    (backgroundContractionExpr Sum.inl i j).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      lowerJetContraction (C.matrix g x)⁻¹ (C.jet g0 x).second i j := by
  change _ = secondJetSource (C.matrix g x) (C.jet g0 x).second i j
  simpa only [nativeJet_compatible_background, compatibleMatrix] using
    eval_backgroundContractionExpr (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl i j x

theorem eval_lowerPerturbationExpr_compatible (i j : Fin n) (x : M) :
    (lowerPerturbationExpr Sum.inl i j).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      lowerJetContraction (C.matrix g x)⁻¹ (C.jet g0 x).second i j +
        lowerJetSource (C.jet g0 x) (backgroundLowerJet (C.jet g x)) i j := by
  change _ = secondJetSource (C.matrix g x) (C.jet g0 x).second i j +
    ricciDeTurckSource (C.jet g0 x) (eraseSecondJet (C.jet g x)) i j
  simpa only [nativeJet_compatible_background, nativeJet_compatible_current, compatibleMatrix] using
    eval_lowerPerturbationExpr (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl i j x

theorem ordered_sourceExpr_compatible (i j : Fin n) (w : List iota) (x : M) :
    ((sourceExpr Sum.inl false i j).orderedDerivative (w.map Sum.inr)).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      directionalWord F w (fun y => ricciDeTurckSource (C.jet g0 y) (C.jet g y) i j) x := by
  simpa only [nativeJet_compatible_background, nativeJet_compatible_current,
    directionalWord_combined_inr] using
      ordered_sourceExpr_native (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl
        (compatibleMatrix_contMDiff C g0 g) (compatibleMatrix_det_ne_zero C g0 g)
        false i j (w.map Sum.inr) x

theorem ordered_lower_sourceExpr_compatible (i j : Fin n) (w : List iota) (x : M) :
    ((sourceExpr Sum.inl true i j).orderedDerivative (w.map Sum.inr)).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      directionalWord F w (fun y =>
        lowerJetSource (C.jet g0 y) (backgroundLowerJet (C.jet g y)) i j) x := by
  change _ = directionalWord F w (fun y =>
    ricciDeTurckSource (C.jet g0 y) (eraseSecondJet (C.jet g y)) i j) x
  simpa only [nativeJet_erase_current, nativeJet_compatible_background,
    nativeJet_compatible_current, directionalWord_combined_inr] using
      ordered_sourceExpr_native (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl
        (compatibleMatrix_contMDiff C g0 g) (compatibleMatrix_det_ne_zero C g0 g)
        true i j (w.map Sum.inr) x

theorem ordered_lowerPerturbationExpr_compatible (i j : Fin n) (w : List iota) (x : M) :
    ((lowerPerturbationExpr Sum.inl i j).orderedDerivative (w.map Sum.inr)).eval
        (nativeValues (combinedFields F C) (compatibleMatrix C g0 g) x) =
      directionalWord F w (fun y =>
        lowerJetContraction (C.matrix g y)⁻¹ (C.jet g0 y).second i j +
          lowerJetSource (C.jet g0 y) (backgroundLowerJet (C.jet g y)) i j) x := by
  change _ = directionalWord F w (fun y =>
    secondJetSource (C.matrix g y) (C.jet g0 y).second i j +
      ricciDeTurckSource (C.jet g0 y) (eraseSecondJet (C.jet g y)) i j) x
  simpa only [nativeJet_compatible_background, nativeJet_compatible_current,
    directionalWord_combined_inr, compatibleMatrix] using
      ordered_lowerPerturbationExpr_native (combinedFields F C) (compatibleMatrix C g0 g) Sum.inl
        (compatibleMatrix_contMDiff C g0 g) (compatibleMatrix_det_ne_zero C g0 g)
        i j (w.map Sum.inr) x

end Compatible

end PoincareConjecture.DeTurckSourceJetNative

end

import PoincareConjecture.Proofs.M03.Existence.DeTurckInverseCompositionNative

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.DeTurckRationalJetNative

universe u v

inductive Atom (iota : Type u) (n : ℕ) where
  | metric (background : Bool) (word : List iota) (i j : Fin n)
  | inverse (background : Bool) (i j : Fin n)
  deriving DecidableEq

def Atom.weight {iota : Type u} {n : ℕ} : Atom iota n → ℕ
  | .metric _ w _ _ => w.length
  | .inverse _ _ _ => 0

inductive Expr (iota : Type u) (n : ℕ) where
  | constant (c : ℝ)
  | atom (a : Atom iota n)
  | add (p q : Expr iota n)
  | mul (p q : Expr iota n)
  | neg (p : Expr iota n)

namespace Expr

variable {iota : Type u} {n : ℕ}

def eval (values : Atom iota n → ℝ) : Expr iota n → ℝ
  | .constant c => c
  | .atom a => values a
  | .add p q => eval values p + eval values q
  | .mul p q => eval values p * eval values q
  | .neg p => -eval values p

def degree : Expr iota n → ℕ
  | .constant _ => 0
  | .atom a => a.weight
  | .add p q => max p.degree q.degree
  | .mul p q => p.degree + q.degree
  | .neg p => p.degree

def metricOrder (b : Bool) : Expr iota n → ℕ
  | .constant _ => 0
  | .atom (.metric c w _ _) => if c = b then w.length else 0
  | .atom (.inverse _ _ _) => 0
  | .add p q => max (p.metricOrder b) (q.metricOrder b)
  | .mul p q => max (p.metricOrder b) (q.metricOrder b)
  | .neg p => p.metricOrder b

def sumList {α : Type*} (l : List α) (f : α → Expr iota n) : Expr iota n :=
  l.foldr (fun a p => .add (f a) p) (.constant 0)

theorem eval_sumList {α : Type*} (l : List α) (f : α → Expr iota n)
    (values : Atom iota n → ℝ) :
    (sumList l f).eval values = (l.map (fun a => (f a).eval values)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [sumList, List.foldr_cons, eval,
      List.map_cons, List.sum_cons] using congrArg ((f a).eval values + ·) ih

theorem degree_sumList_le {α : Type*} (l : List α) (f : α → Expr iota n)
    (k : ℕ) (hf : ∀ a ∈ l, (f a).degree ≤ k) :
    (sumList l f).degree ≤ k := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    exact max_le (hf a List.mem_cons_self)
      (ih (fun b hb => hf b (List.mem_cons_of_mem a hb)))

def sumFin (f : Fin n → Expr iota n) : Expr iota n :=
  sumList (List.finRange n) f

theorem eval_sumFin (f : Fin n → Expr iota n) (values : Atom iota n → ℝ) :
    (sumFin f).eval values = ∑ i, (f i).eval values := by
  rw [sumFin, eval_sumList]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

theorem degree_sumFin_le (f : Fin n → Expr iota n) (k : ℕ)
    (hf : ∀ a, (f a).degree ≤ k) : (sumFin f).degree ≤ k :=
  degree_sumList_le _ _ k (fun a _ => hf a)

theorem metricOrder_sumList_le {α : Type*} (l : List α) (f : α → Expr iota n)
    (b : Bool) (k : ℕ) (hf : ∀ a ∈ l, (f a).metricOrder b ≤ k) :
    (sumList l f).metricOrder b ≤ k := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    exact max_le (hf a List.mem_cons_self)
      (ih (fun c hc => hf c (List.mem_cons_of_mem a hc)))

theorem metricOrder_sumFin_le (f : Fin n → Expr iota n) (b : Bool) (k : ℕ)
    (hf : ∀ a, (f a).metricOrder b ≤ k) : (sumFin f).metricOrder b ≤ k :=
  metricOrder_sumList_le _ _ b k (fun a _ => hf a)

def atomDerivative (a : iota) : Atom iota n → Expr iota n
  | .metric b w i j => .atom (.metric b (a :: w) i j)
  | .inverse b i j => .neg (sumFin (fun k => sumFin (fun l =>
      .mul (.mul (.atom (.inverse b i k)) (.atom (.metric b [a] k l)))
        (.atom (.inverse b l j)))))

def derivative (a : iota) : Expr iota n → Expr iota n
  | .constant _ => .constant 0
  | .atom v => atomDerivative a v
  | .add p q => .add (derivative a p) (derivative a q)
  | .mul p q => .add (.mul (derivative a p) q) (.mul p (derivative a q))
  | .neg p => .neg (derivative a p)

def orderedDerivative : List iota → Expr iota n → Expr iota n
  | [], p => p
  | a :: w, p => derivative a (orderedDerivative w p)

theorem degree_atomDerivative_le (a : iota) (v : Atom iota n) :
    (atomDerivative a v).degree ≤ v.weight + 1 := by
  cases v with
  | metric b w i j => simp [atomDerivative, degree, Atom.weight]
  | inverse b i j =>
    apply degree_sumFin_le
    intro k
    apply degree_sumFin_le
    intro l
    simp [degree, Atom.weight]

theorem degree_derivative_le (a : iota) (p : Expr iota n) :
    (p.derivative a).degree ≤ p.degree + 1 := by
  induction p with
  | constant c => exact Nat.zero_le _
  | atom v => exact degree_atomDerivative_le a v
  | add p q hp hq =>
    change max _ _ ≤ max p.degree q.degree + 1
    exact max_le (hp.trans (Nat.add_le_add_right (le_max_left _ _) 1))
      (hq.trans (Nat.add_le_add_right (le_max_right _ _) 1))
  | mul p q hp hq =>
    change max ((derivative a p).degree + q.degree)
      (p.degree + (derivative a q).degree) ≤ p.degree + q.degree + 1
    omega
  | neg p hp => exact hp

theorem degree_orderedDerivative_le (w : List iota) (p : Expr iota n) :
    (p.orderedDerivative w).degree ≤ p.degree + w.length := by
  induction w with
  | nil => exact le_rfl
  | cons a w ih =>
    have h := degree_derivative_le a (p.orderedDerivative w)
    simp only [orderedDerivative, List.length_cons]
    omega

theorem metricOrder_atomDerivative_le (a : iota) (v : Atom iota n) (b : Bool) :
    (atomDerivative a v).metricOrder b ≤ (Expr.atom v).metricOrder b + 1 := by
  cases v with
  | metric c w i j =>
    by_cases h : c = b <;> simp [atomDerivative, metricOrder, h]
  | inverse c i j =>
    apply metricOrder_sumFin_le
    intro k
    apply metricOrder_sumFin_le
    intro l
    by_cases h : c = b <;> simp [metricOrder, h]

theorem metricOrder_derivative_le (a : iota) (p : Expr iota n) (b : Bool) :
    (p.derivative a).metricOrder b ≤ p.metricOrder b + 1 := by
  induction p with
  | constant c => exact Nat.zero_le _
  | atom v => exact metricOrder_atomDerivative_le a v b
  | add p q hp hq =>
    change max _ _ ≤ max (p.metricOrder b) (q.metricOrder b) + 1
    exact max_le (hp.trans (Nat.add_le_add_right (le_max_left _ _) 1))
      (hq.trans (Nat.add_le_add_right (le_max_right _ _) 1))
  | mul p q hp hq =>
    change max (max _ _) (max _ _) ≤ max (p.metricOrder b) (q.metricOrder b) + 1
    omega
  | neg p hp => exact hp

theorem metricOrder_orderedDerivative_le (w : List iota) (p : Expr iota n) (b : Bool) :
    (p.orderedDerivative w).metricOrder b ≤ p.metricOrder b + w.length := by
  induction w with
  | nil => exact le_rfl
  | cons a w ih =>
    have h := metricOrder_derivative_le a (p.orderedDerivative w) b
    simp only [orderedDerivative, List.length_cons]
    omega

def atoms : Expr iota n → Finset (Atom iota n) := by
  classical
  exact fun p => match p with
    | .constant _ => ∅
    | .atom a => {a}
    | .add p q => p.atoms ∪ q.atoms
    | .mul p q => p.atoms ∪ q.atoms
    | .neg p => p.atoms

theorem eval_congr_atoms (p : Expr iota n) (values values' : Atom iota n → ℝ)
    (h : ∀ a ∈ p.atoms, values a = values' a) : p.eval values = p.eval values' := by
  classical
  induction p with
  | constant c => rfl
  | atom a => exact h a (Finset.mem_singleton_self a)
  | add p q hp hq =>
    exact congrArg₂ (· + ·)
      (hp (fun a ha => h a (Finset.mem_union_left _ ha)))
      (hq (fun a ha => h a (Finset.mem_union_right _ ha)))
  | mul p q hp hq =>
    exact congrArg₂ (· * ·)
      (hp (fun a ha => h a (Finset.mem_union_left _ ha)))
      (hq (fun a ha => h a (Finset.mem_union_right _ ha)))
  | neg p hp => exact congrArg Neg.neg (hp h)

theorem weight_le_degree_of_mem (p : Expr iota n) (a : Atom iota n)
    (ha : a ∈ p.atoms) : a.weight ≤ p.degree := by
  classical
  induction p with
  | constant c => exact False.elim (Finset.notMem_empty a ha)
  | atom b =>
    have h : a = b := Finset.mem_singleton.mp ha
    subst a
    exact le_rfl
  | add p q hp hq =>
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (hp ha).trans (le_max_left _ _)
    · exact (hq ha).trans (le_max_right _ _)
  | mul p q hp hq =>
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (hp ha).trans (Nat.le_add_right _ _)
    · exact (hq ha).trans (Nat.le_add_left _ _)
  | neg p hp => exact hp ha

theorem word_length_le_metricOrder_of_mem (p : Expr iota n) (b : Bool)
    (w : List iota) (i j : Fin n) (ha : Atom.metric b w i j ∈ p.atoms) :
    w.length ≤ p.metricOrder b := by
  classical
  induction p with
  | constant c => exact False.elim (Finset.notMem_empty _ ha)
  | atom a =>
    have h : Atom.metric b w i j = a := Finset.mem_singleton.mp ha
    subst a
    simp [metricOrder]
  | add p q hp hq =>
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (hp ha).trans (le_max_left _ _)
    · exact (hq ha).trans (le_max_right _ _)
  | mul p q hp hq =>
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (hp ha).trans (le_max_left _ _)
    · exact (hq ha).trans (le_max_right _ _)
  | neg p hp => exact hp ha

def finiteValues (p : Expr iota n) (values : p.atoms → ℝ) (a : Atom iota n) : ℝ := by
  classical
  exact if ha : a ∈ p.atoms then values ⟨a, ha⟩ else 0

theorem eval_finiteValues (p : Expr iota n) (values : Atom iota n → ℝ) :
    p.eval (p.finiteValues (fun a => values a.val)) = p.eval values := by
  apply p.eval_congr_atoms
  intro a ha
  simp only [finiteValues, dif_pos ha]

end Expr

open TensorProbeNative DeTurckInverseCompositionNative

variable {iota : Type u} {n : ℕ} {M : Type v}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [Fintype iota]

def nativeValues (F : iota → SmoothField (n := n) (M := M))
    (G : Bool → M → Matrix (Fin n) (Fin n) ℝ) (x : M) : Atom iota n → ℝ
  | .metric b w i j => directionalWord F w (fun y => G b y i j) x
  | .inverse b i j => (G b x)⁻¹ i j

theorem nativeValues_contMDiff (F : iota → SmoothField (n := n) (M := M))
    (G : Bool → M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => G b x i j))
    (hdet : ∀ b x, (G b x).det ≠ 0) (v : Atom iota n) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => nativeValues F G x v) := by
  cases v with
  | metric b w i j =>
    exact directionalWord_contMDiff F w (fun x =>
      contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hG b x) i) j)
  | inverse b i j => exact inverse_entry_contMDiff (G b) (hG b) (hdet b) i j

theorem Expr.native_contMDiff (p : Expr iota n)
    (F : iota → SmoothField (n := n) (M := M))
    (G : Bool → M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => G b x i j))
    (hdet : ∀ b x, (G b x).det ≠ 0) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => p.eval (nativeValues F G x)) := by
  induction p with
  | constant c => exact contMDiff_const
  | atom v => exact nativeValues_contMDiff F G hG hdet v
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq
  | neg p hp => exact hp.neg

theorem atomDerivative_native (F : iota → SmoothField (n := n) (M := M))
    (G : Bool → M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => G b x i j))
    (hdet : ∀ b x, (G b x).det ≠ 0) (a : iota) (v : Atom iota n) (x : M) :
    (Expr.atomDerivative a v).eval (nativeValues F G x) =
      scalarDirectional (F a) (fun y => nativeValues F G y v) x := by
  cases v with
  | metric b w i j => rfl
  | inverse b i j =>
    simp only [Expr.atomDerivative, Expr.eval, Expr.eval_sumFin, nativeValues]
    exact (DeTurckNative.mvfderiv_matrix_inv_entry (G b)
      ((hG b x).of_le (by simp)) (hdet b x) (F a x) i j).symm

theorem Expr.derivative_native (p : Expr iota n)
    (F : iota → SmoothField (n := n) (M := M))
    (G : Bool → M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => G b x i j))
    (hdet : ∀ b x, (G b x).det ≠ 0) (a : iota) (x : M) :
    (p.derivative a).eval (nativeValues F G x) =
      scalarDirectional (F a) (fun y => p.eval (nativeValues F G y)) x := by
  induction p with
  | constant c =>
    change 0 = mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun _ : M => c) x (F a x)
    simp only [mfderiv_const, ContinuousLinearMap.zero_apply]
  | atom v => exact atomDerivative_native F G hG hdet a v x
  | add p q hp hq =>
    have hd := congrArg (fun L : TangentSpace (𝓡 n) x →L[ℝ] ℝ => L (F a x))
      (mfderiv_add ((p.native_contMDiff F G hG hdet).mdifferentiable (by simp) x)
        ((q.native_contMDiff F G hG hdet).mdifferentiable (by simp) x))
    simp only [Expr.derivative, Expr.eval, hp, hq]
    exact hd.symm
  | mul p q hp hq =>
    have hd := scalarDirectional_mul (F a)
      ((p.native_contMDiff F G hG hdet).mdifferentiable (by simp) x)
      ((q.native_contMDiff F G hG hdet).mdifferentiable (by simp) x)
    simp only [Expr.derivative, Expr.eval, hp, hq]
    rw [hd]
    ring
  | neg p hp =>
    simp only [Expr.derivative, Expr.eval, hp]
    exact (scalarDirectional_neg (F a)
      (fun y => p.eval (nativeValues F G y)) x).symm

theorem Expr.orderedDerivative_native (p : Expr iota n)
    (F : iota → SmoothField (n := n) (M := M))
    (G : Bool → M → Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ b, ContMDiff (𝓡 n) 𝓘(ℝ, Fin n → Fin n → ℝ) ∞
      (fun x i j => G b x i j))
    (hdet : ∀ b x, (G b x).det ≠ 0) (w : List iota) (x : M) :
    (p.orderedDerivative w).eval (nativeValues F G x) =
      directionalWord F w (fun y => p.eval (nativeValues F G y)) x := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    rw [Expr.orderedDerivative, Expr.derivative_native _ F G hG hdet]
    exact congrArg (fun f : M → ℝ => scalarDirectional (F a) f x) (funext ih)

end PoincareConjecture.DeTurckRationalJetNative

end

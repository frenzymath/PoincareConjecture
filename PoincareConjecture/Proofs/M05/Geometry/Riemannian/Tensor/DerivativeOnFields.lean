
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.LocalCalculus
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality








set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


noncomputable def covariantTensorDerivativeOnFields
    (D : LeviCivitaData g) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (X : (x : M) → TangentSpace (𝓡 n) x)
    (Y : Fin k → (x : M) → TangentSpace (𝓡 n) x) (x : M) : ℝ :=
  mvfderiv (𝓡 n) (fun y => T y (fun i => Y i y)) x (X x) -
    ∑ i, T x (Function.update (fun j => Y j x) i
      (D.connection (Y i) x (X x)))



lemma covariantTensorDerivative_two_on_fields
    (D : LeviCivitaData g) {T : CovariantTensorEvaluation n M 2}
    (hT : IsSmoothCovariantTensor T)
    (Y Z : (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x)
    (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Z) x)
    (u : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative T x ![u, Y x, Z x] =
      mvfderiv (𝓡 n) (fun y => T y ![Y y, Z y]) x u -
        T x ![D.connection Y x u, Z x] -
        T x ![Y x, D.connection Z x u] := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  choose A hA using hT.1
  let B : (y : M) → TangentSpace (𝓡 n) y →ₗ[ℝ] TangentSpace (𝓡 n) y →ₗ[ℝ] ℝ :=
    fun y => bilinearOfTwoTensor (A y)
  have hB (y : M) (a b : TangentSpace (𝓡 n) y) : B y a b = T y ![a, b] :=
    (hA y _).symm
  have hd (Y Z : (y : M) → TangentSpace (𝓡 n) y)
      (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x)
      (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Z) x) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) (fun y => B y (Y y) (Z y)) x := by
    simp_rw [hB]
    convert hT.mdifferentiableAt_apply (X := ![Y, Z])
      (fun i => by fin_cases i <;> assumption) using 1
    funext y
    congr 1
    ext i
    fin_cases i <;> rfl
  let Φ := fun (Y Z : (y : M) → TangentSpace (𝓡 n) y) =>
    mvfderiv (𝓡 n) (fun y => B y (Y y) (Z y)) x u -
      B x (D.connection Y x u) (Z x) - B x (Y x) (D.connection Z x u)
  have hΦ₁ (Z : (y : M) → TangentSpace (𝓡 n) y)
      (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Z) x) :
      TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n)) (fun Y => Φ Y Z) x := by
    constructor
    · intro f Y hf hY
      simp [Φ, mvfderiv_fun_mul hf (hd Y Z hY hZ),
        D.connection.isCovariantDerivativeOn.leibniz hY hf,
        map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
      ring
    · intro Y Y' hY hY'
      simp [Φ, mvfderiv_fun_add (hd Y Z hY hZ) (hd Y' Z hY' hZ),
        D.connection.isCovariantDerivativeOn.add hY hY',
        map_add, LinearMap.add_apply]
      ring
  have hΦ₂ (Y : (y : M) → TangentSpace (𝓡 n) y)
      (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x) :
      TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n)) (fun Z => Φ Y Z) x := by
    constructor
    · intro f Z hf hZ
      simp [Φ, mvfderiv_fun_mul hf (hd Y Z hY hZ),
        D.connection.isCovariantDerivativeOn.leibniz hZ hf,
        map_add, map_smul]
      ring
    · intro Z Z' hZ hZ'
      simp [Φ, mvfderiv_fun_add (hd Y Z hY hZ) (hd Y Z' hY hZ'),
        D.connection.isCovariantDerivativeOn.add hZ hZ', map_add]
      ring
  have heq := TensorialAt.pointwise₂ hΦ₁ hΦ₂ hY
    (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (Y x))
    hZ (FiberBundle.mdifferentiableAt_extend (𝓡 n) (EuclideanSpace ℝ (Fin n)) (Z x))
    (by simp) (by simp)
  simp only [Φ, hB, FiberBundle.extend_apply_self] at heq
  rw [heq]
  simp [covariantTensorDerivative, Fin.sum_univ_two]
  have hu0 (a b c : TangentSpace (𝓡 n) x) :
      Function.update ![a, b] 0 c = ![c, b] := by
    ext i
    fin_cases i <;> simp
  have hu1 (a b c : TangentSpace (𝓡 n) x) :
      Function.update ![a, b] 1 c = ![a, c] := by
    ext i
    fin_cases i <;> simp
  have hv (y : M) : (fun i : Fin 2 =>
      FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (![Y x, Z x] i) y) =
      ![FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y x) y,
        FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Z x) y] := by
    ext i
    fin_cases i <;> rfl
  simp_rw [hu0, hu1, hv]
  ring

lemma covariantTensorDerivativeOnFields_apply_extend
    (D : LeviCivitaData g) {k : ℕ} (T : CovariantTensorEvaluation n M k)
    (x : M) (u : TangentSpace (𝓡 n) x)
    (v : Fin k → TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivativeOnFields T
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u)
        (fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)) x =
      D.covariantTensorDerivative T x (Fin.cons u v) := by
  simp only [covariantTensorDerivativeOnFields, covariantTensorDerivative,
    Fin.cons_zero, Fin.cons_succ, FiberBundle.extend_apply_self]

private lemma covariantTensorDerivativeOnFields_tensorial
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (X : (y : M) → TangentSpace (𝓡 n) y)
    (Y : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hY : ∀ j, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (Y j)) x)
    (i : Fin k) :
    TensorialAt (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (fun Z => D.covariantTensorDerivativeOnFields T X (Function.update Y i Z) x) x := by
  classical
  choose A hA using hT.1
  have heval (Z : (y : M) → TangentSpace (𝓡 n) y) (y : M) :
      (fun j => Function.update Y i Z j y) =
        Function.update (fun j => Y j y) i (Z y) := by
    ext j
    by_cases h : j = i <;> simp [h, Function.update_of_ne]
  have hd (Z : (y : M) → TangentSpace (𝓡 n) y)
      (hZ : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Z) x) :
      MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun y => A y (Function.update (fun j => Y j y) i (Z y))) x := by
    simp_rw [← hA, ← heval]
    apply hT.mdifferentiableAt_apply
    intro j
    by_cases h : j = i <;> simp [h, Function.update_of_ne, hY, hZ]
  have hexp (Z : (y : M) → TangentSpace (𝓡 n) y) :
      D.covariantTensorDerivativeOnFields T X (Function.update Y i Z) x =
        mvfderiv (𝓡 n)
          (fun y => A y (Function.update (fun j => Y j y) i (Z y))) x (X x) -
        A x (Function.update (fun j => Y j x) i (D.connection Z x (X x))) -
        ∑ j ∈ Finset.univ.erase i, A x
          (Function.update (Function.update (fun l => Y l x) j
            (D.connection (Y j) x (X x))) i (Z x)) := by
    unfold covariantTensorDerivativeOnFields
    simp_rw [heval, hA]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Function.update_self, Function.update_idem]
    have hs : (∑ j ∈ Finset.univ.erase i,
        A x (Function.update (Function.update (fun l => Y l x) i (Z x)) j
          (D.connection (Function.update Y i Z j) x (X x)))) =
        ∑ j ∈ Finset.univ.erase i, A x
          (Function.update (Function.update (fun l => Y l x) j
            (D.connection (Y j) x (X x))) i (Z x)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      rw [Function.update_of_ne hji, Function.update_comm hji.symm]
    rw [hs]
    ring
  constructor
  · intro f Z hf hZ
    simp only [hexp, Pi.smul_apply', MultilinearMap.map_update_smul, smul_eq_mul]
    rw [mvfderiv_fun_mul hf (hd Z hZ),
      D.connection.isCovariantDerivativeOn.leibniz hZ hf]
    simp [MultilinearMap.map_update_add, MultilinearMap.map_update_smul,
      smul_eq_mul, ← Finset.mul_sum]
    ring
  · intro Z W hZ hW
    simp only [hexp, Pi.add_apply, MultilinearMap.map_update_add]
    rw [mvfderiv_fun_add (hd Z hZ) (hd W hW),
      D.connection.isCovariantDerivativeOn.add hZ hW]
    simp [MultilinearMap.map_update_add, Finset.sum_add_distrib]
    ring



lemma covariantTensorDerivativeOnFields_congr
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (X : (y : M) → TangentSpace (𝓡 n) y)
    (Y Z : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hY : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (Y i)) x)
    (hZ : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (Z i)) x)
    (hYZ : ∀ i, Y i x = Z i x) :
    D.covariantTensorDerivativeOnFields T X Y x =
      D.covariantTensorDerivativeOnFields T X Z x := by
  classical
  have hW (s : Finset (Fin k)) (i : Fin k) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
        (T% (s.piecewise Z Y i)) x := by
    by_cases hi : i ∈ s
    · simpa [Finset.piecewise, hi] using hZ i
    · simpa [Finset.piecewise, hi] using hY i
  have hs (s : Finset (Fin k)) :
      D.covariantTensorDerivativeOnFields T X (s.piecewise Z Y) x =
        D.covariantTensorDerivativeOnFields T X Y x := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.piecewise_insert]
      have h := (covariantTensorDerivativeOnFields_tensorial D hT X
        (s.piecewise Z Y) x (hW s) i).pointwise (hZ i) (hW s i)
          (by simpa [Finset.piecewise, hi] using (hYZ i).symm)
      simp only [Function.update_eq_self] at h
      exact h.trans ih
  simpa using (hs Finset.univ).symm



lemma covariantTensorDerivative_on_fields
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T)
    (Y : Fin k → (y : M) → TangentSpace (𝓡 n) y) (x : M)
    (hY : ∀ i, MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% (Y i)) x)
    (u : TangentSpace (𝓡 n) x) :
    D.covariantTensorDerivative T x (Fin.cons u (fun i => Y i x)) =
      mvfderiv (𝓡 n) (fun y => T y (fun i => Y i y)) x u -
        ∑ i, T x (Function.update (fun j => Y j x) i (D.connection (Y i) x u)) := by
  have h := D.covariantTensorDerivativeOnFields_congr hT
    (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u) Y
    (fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (Y i x)) x hY
    (fun i => FiberBundle.mdifferentiableAt_extend (𝓡 n)
      (EuclideanSpace ℝ (Fin n)) (Y i x)) (fun i => by simp)
  rw [D.covariantTensorDerivativeOnFields_apply_extend] at h
  simpa only [covariantTensorDerivativeOnFields, FiberBundle.extend_apply_self] using h.symm

end PoincareConjecture.LeviCivitaData

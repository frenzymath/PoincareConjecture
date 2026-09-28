import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.DerivativeOnFields
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.LocalRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Filter Set

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private lemma derivative_slot_tensorial
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

private lemma derivative_tail_slot_linear
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) (x : M) (u : TangentSpace (𝓡 n) x)
    (v : Fin k → TangentSpace (𝓡 n) x) (i : Fin k) :
    ∃ L : TangentSpace (𝓡 n) x →ₗ[ℝ] ℝ, ∀ z,
      D.covariantTensorDerivative T x (Fin.cons u (Function.update v i z)) = L z := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let X := FiberBundle.extend E u
  let Y := fun j => FiberBundle.extend E (v j)
  let Φ := fun Z => D.covariantTensorDerivativeOnFields T X (Function.update Y i Z) x
  have hΦ : TensorialAt (𝓡 n) E Φ x :=
    derivative_slot_tensorial D hT X Y x
      (fun j => FiberBundle.mdifferentiableAt_extend (𝓡 n) E (v j)) i
  refine ⟨(TensorialAt.mkHom Φ x hΦ).toLinearMap, ?_⟩
  intro z
  change _ = Φ (FiberBundle.extend E z)
  rw [← D.covariantTensorDerivativeOnFields_apply_extend T x u]
  congr 1
  funext j
  by_cases h : j = i <;> simp [Y, E, h, Function.update_of_ne]

theorem covariantTensorDerivative_isSmooth
    (D : LeviCivitaData g) {k : ℕ} {T : CovariantTensorEvaluation n M k}
    (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (D.covariantTensorDerivative T) := by
  classical
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 x
    let d : DecidableEq (Fin (k + 1)) := inferInstance
    refine ⟨{
      toFun := D.covariantTensorDerivative T x
      map_update_add' := ?_
      map_update_smul' := ?_ }, fun _ => rfl⟩
    · intro d' v i a b
      cases Subsingleton.elim d' d
      rw [← Fin.cons_self_tail v]
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.update_cons_zero, covariantTensorDerivative,
          Fin.cons_zero, Fin.cons_succ, map_add, hA,
          MultilinearMap.map_update_add, Finset.sum_add_distrib]
        ring
      | succ i =>
        obtain ⟨L, hL⟩ := derivative_tail_slot_linear D hT x (v 0) (Fin.tail v) i
        simp only [← Fin.cons_update, hL, map_add]
    · intro d' v i c a
      cases Subsingleton.elim d' d
      rw [← Fin.cons_self_tail v]
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.update_cons_zero, covariantTensorDerivative,
          Fin.cons_zero, Fin.cons_succ, map_smul, hA,
          MultilinearMap.map_update_smul, smul_eq_mul, ← Finset.mul_sum]
        ring
      | succ i =>
        obtain ⟨L, hL⟩ := derivative_tail_slot_linear D hT x (v 0) (Fin.tail v) i
        simp only [← Fin.cons_update, hL, map_smul]
  · intro U hU X hX x hx
    have hXat (i : Fin (k + 1)) := (hX i x hx).contMDiffAt (hU.mem_nhds hx)
    have heval := hT.contMDiffAt_apply (X := fun i => X i.succ) (fun i => hXat i.succ)
    have hfirst := contMDiffAt_mvfderiv_apply heval (hXat 0)
    have hterm (i : Fin k) : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
        (fun y => T y (Function.update (fun j => X j.succ y) i
          (D.connection (X i.succ) y (X 0 y)))) x := by
      have hi := D.contMDiffAt_covariantDerivativeOnFields (hXat 0) (hXat i.succ)
      have h := hT.contMDiffAt_apply (x := x)
        (X := Function.update (fun j => X j.succ) i
          (D.covariantDerivativeOnFields (X 0) (X i.succ)))
        (fun j => by by_cases hj : j = i <;> simp [hj, Function.update_of_ne, hXat, hi])
      convert h using 1
      funext y
      congr 1
      funext j
      by_cases hj : j = i <;>
        simp [hj, Function.update_of_ne, covariantDerivativeOnFields]
    have hsmooth := hfirst.sub (ContMDiffAt.sum (t := Finset.univ) fun i _ => hterm i)
    apply (hsmooth.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU.mem_nhds hx] with y hy
    have hY (i : Fin k) := ((hX i.succ y hy).contMDiffAt
      (hU.mem_nhds hy)).mdifferentiableAt (by simp)
    have hcons : Fin.cons (X 0 y) (fun i => X i.succ y) = (fun i => X i y) := by
      ext i
      cases i using Fin.cases <;> rfl
    simpa only [hcons] using
      (D.covariantTensorDerivative_on_fields hT (fun i => X i.succ) y hY (X 0 y))

end PoincareConjecture.LeviCivitaData

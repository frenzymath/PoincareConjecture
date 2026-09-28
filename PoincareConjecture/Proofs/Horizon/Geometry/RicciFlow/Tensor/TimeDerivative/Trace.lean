import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.Matrix
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Trace








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter Set

universe u

namespace PoincareConjecture.RicciFlow

private lemma hasDerivAt_matrix_inv_entry_at_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : ℝ → Matrix ι ι ℝ) (G' : Matrix ι ι ℝ) {t : ℝ}
    (hG : ∀ i j, ContDiffAt ℝ ∞ (fun s => G s i j) t)
    (hd : ∀ i j, HasDerivAt (fun s => G s i j) (G' i j) t)
    (hx : G t = 1) (i j : ι) :
    HasDerivAt (fun s => (G s)⁻¹ i j) (-G' i j) t := by
  have hdet : (G t).det ≠ 0 := by simp [hx]
  have hs (a b : ι) := (Poincare.Manifold.contMDiffAt_matrix_inv_entry G t
    (fun a b => (hG a b).contMDiffAt) hdet a b).contDiffAt
  have hi (a b : ι) := ((hs a b).differentiableAt (by simp)).hasDerivAt
  have hnear : ∀ᶠ s in 𝓝 t, (G s).det ≠ 0 :=
    (Poincare.Manifold.contMDiffAt_matrix_det G t
      (fun a b => (hG a b).contMDiffAt)).continuousAt.eventually_ne hdet
  have heq : (fun s => ∑ a, (G s)⁻¹ i a * G s a j) =ᶠ[𝓝 t]
      (fun _ => (1 : Matrix ι ι ℝ) i j) := by
    filter_upwards [hnear] with s hs
    exact congrArg (fun A : Matrix ι ι ℝ => A i j)
      (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hs))
  have hsum := HasDerivAt.sum (u := Finset.univ) fun a _ => (hi i a).mul (hd a j)
  have hz := hsum.unique ((hasDerivAt_const t ((1 : Matrix ι ι ℝ) i j)).congr_of_eventuallyEq
    (by
      convert heq using 1
      ext s
      simp only [Finset.sum_apply, Pi.mul_apply]))
  simp only [hx, inv_one, Matrix.one_apply, Finset.sum_add_distrib] at hz
  simp at hz
  exact (hi i j).congr_deriv (by linarith)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


lemma hasDerivAt_tensorTrace
    (F : RicciFlow n M J) {k : ℕ} {T W : ℝ → CovariantTensorEvaluation n M (k + 2)}
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hW : ∀ z : Fin (k + 2) → TangentSpace (𝓡 n) x,
      HasDerivAt (fun s => T s x z) (W t x z) t)
    (v : Fin k → TangentSpace (𝓡 n) x) :
    let b := (F.metric t).orthonormalBasis x
    HasDerivAt (fun s => (F.metric s).tensorTrace (T s) x v)
      ((F.metric t).tensorTrace (W t) x v +
        2 * ∑ i, ∑ j, (F.connection t).ricci x (b i) (b j) *
          T t x (Fin.cons (b i) (Fin.cons (b j) v))) t := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let b := (F.metric t).orthonormalBasis x
  let c := b.toBasis
  let G : ℝ → Matrix _ _ ℝ := fun s i j => (F.metric s).inner x (b i) (b j)
  have hGx : G t = 1 := by ext i j; exact b.inner_eq_ite i j
  have hG (i j) := F.contDiffAt_inner_time ht x (b i) (b j)
  have hd (i j) := (F.equation t (interior_subset ht) x (b i) (b j)).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)
  have hi (i j) := hasDerivAt_matrix_inv_entry_at_one G
    (fun i j => -2 * (F.connection t).ricci x (b i) (b j)) hG hd hGx i j
  have hsum := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    HasDerivAt.sum (u := Finset.univ) fun j _ =>
      (hi i j).mul (hW (Fin.cons (b i) (Fin.cons (b j) v)))
  have heq (s : ℝ) : (F.metric s).tensorTrace (T s) x v =
      ∑ i, ∑ j, (G s)⁻¹ i j * T s x (Fin.cons (b i) (Fin.cons (b j) v)) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨(F.metric s).toRiemannianMetric⟩
    obtain ⟨A, hA⟩ := (hT s).1 x
    have h := bilinear_sum_basis_eq_inverse_gram (bilinearOfTensorCons A v)
      c ((F.metric s).orthonormalBasis x)
    change (∑ i, A (Fin.cons ((F.metric s).orthonormalBasis x i)
      (Fin.cons ((F.metric s).orthonormalBasis x i) v))) =
      ∑ i, ∑ j, (Matrix.of (fun i j => (F.metric s).inner x (b i) (b j)))⁻¹ i j *
        A (Fin.cons (b i) (Fin.cons (b j) v)) at h
    simp only [← hA] at h
    exact h
  have h := hsum.congr_of_eventuallyEq
    (Eventually.of_forall fun s => by
      convert heq s using 1
      simp only [Finset.sum_apply, Pi.mul_apply])
  apply h.congr_deriv
  simp only [hGx, inv_one, Matrix.one_apply, Finset.sum_add_distrib,
    RiemannianMetric.tensorTrace, neg_mul, neg_neg, ite_mul, one_mul, zero_mul]
  simp only [mul_assoc, ← Finset.mul_sum, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  exact add_comm _ _

end PoincareConjecture.RicciFlow

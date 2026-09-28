import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.Trace
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Tensor.LocalCalculus
import Mathlib.Geometry.Manifold.Algebra.Structures







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
private lemma contMDiffAt_matrix_det {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : M → Matrix ι ι ℝ) (x : M)
    (hG : ∀ i j, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y => G y i j) x) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y => (G y).det) x := by
  simp only [Matrix.det_apply']
  apply ContMDiffAt.sum
  intro σ _
  exact contMDiffAt_const.mul (ContMDiffAt.prod fun i _ => hG (σ i) i)

omit [IsManifold (𝓡 n) ∞ M] in
private lemma contMDiffAt_matrix_inv_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : M → Matrix ι ι ℝ) (x : M)
    (hG : ∀ i j, ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y => G y i j) x)
    (hx : (G x).det ≠ 0) (i j : ι) :
    ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y => (G y)⁻¹ i j) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply]
  apply ((contMDiffAt_matrix_det G x hG).inv₀ hx).mul
  apply contMDiffAt_matrix_det
  intro a b
  by_cases ha : a = j
  · subst a
    simpa using (contMDiffAt_const (I := 𝓡 n) (x := x) (n := ∞)
      (c := (Pi.single i (1 : ℝ) : ι → ℝ) b))
  · simpa [Matrix.updateRow_apply, ha] using hG a b

private lemma eventually_exists_basis_extend {ι : Type} (x : M)
    (b : Module.Basis ι ℝ (TangentSpace (𝓡 n) x)) :
    ∀ᶠ y in nhds x, ∃ c : Module.Basis ι ℝ (TangentSpace (𝓡 n) y),
      ∀ i, c i = FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i) y := by
  let E := EuclideanSpace ℝ (Fin n)
  let V := TangentSpace (𝓡 n) (M := M)
  let e := trivializationAt E V x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E V x
  filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
  let L := (e.continuousLinearEquivAt ℝ x hx).trans
    (e.continuousLinearEquivAt ℝ y hy).symm
  refine ⟨b.map L.toLinearEquiv, fun i => ?_⟩
  change (e.continuousLinearEquivAt ℝ y hy).symm
    ((e.continuousLinearEquivAt ℝ x hx) (b i)) = _
  rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq,
    Bundle.Trivialization.symmL_apply _ hy]
  rfl


lemma IsSmoothCovariantTensor.tensorTrace {g : RiemannianMetric n M} {k : ℕ}
    {T : CovariantTensorEvaluation n M (k + 2)} (hT : IsSmoothCovariantTensor T) :
    IsSmoothCovariantTensor (g.tensorTrace T) := by
  constructor
  · intro x
    obtain ⟨A, hA⟩ := hT.1 x
    refine ⟨∑ i, (A.curryLeft (g.orthonormalBasis x i)).curryLeft
      (g.orthonormalBasis x i), fun v => ?_⟩
    simp only [RiemannianMetric.tensorTrace, sum_apply, hA,
      MultilinearMap.curryLeft_apply]
  · intro U hU V hV x hx
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContMDiffRiemannianBundle (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) := ⟨g.inner, g.contMDiff, fun _ _ _ => rfl⟩
    let b := g.orthonormalBasis x
    let X := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    let G : M → Matrix _ _ ℝ := fun y i j => g.inner y (X i y) (X j y)
    let A : M → Matrix _ _ ℝ := fun y i j =>
      T y (Fin.cons (X i y) (Fin.cons (X j y) (fun a => V a y)))
    have hX (i) : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
        (T% (X i)) x := FiberBundle.contMDiffAt_extend (k := ∞) (𝓡 n) _ (b i)
    have hG (i j) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y => G y i j) x :=
      (hX i).inner_bundle (hX j)
    have hA (i j) : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ (fun y => A y i j) x := by
      apply hT.contMDiffAt_apply
      intro a
      refine Fin.cases (hX i) (fun a => Fin.cases (hX j) (fun a => ?_) a) a
      exact (hV a).contMDiffAt (hU.mem_nhds hx)
    have hGx : G x = 1 := by
      ext i j
      change g.inner x (X i x) (X j x) = _
      simp only [X, FiberBundle.extend_apply_self]
      change inner ℝ (b i) (b j) = _
      exact b.inner_eq_ite i j
    have hinv := contMDiffAt_matrix_inv_entry G x hG (by simp [hGx])
    have heq : (fun y => g.tensorTrace T y (fun a => V a y)) =ᶠ[nhds x]
        (fun y => ∑ i, ∑ j, (G y)⁻¹ i j * A y i j) := by
      filter_upwards [eventually_exists_basis_extend x b.toBasis] with y hy
      obtain ⟨c, hc⟩ := hy
      obtain ⟨B, hB⟩ := hT.1 y
      have h := bilinear_sum_basis_eq_inverse_gram
        (bilinearOfTensorCons B (fun a => V a y)) c (g.orthonormalBasis y)
      change (∑ a, B (Fin.cons (g.orthonormalBasis y a)
        (Fin.cons (g.orthonormalBasis y a) (fun a => V a y)))) =
        ∑ i, ∑ j, (Matrix.of (fun i j => g.inner y (c i) (c j)))⁻¹ i j *
          B (Fin.cons (c i) (Fin.cons (c j) (fun a => V a y))) at h
      simp only [← hB, hc, OrthonormalBasis.coe_toBasis] at h
      change g.tensorTrace T y (fun a => V a y) =
        ∑ i, ∑ j, (G y)⁻¹ i j * A y i j at h
      exact h
    have hs : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞
        (fun y => ∑ i, ∑ j, (G y)⁻¹ i j * A y i j) x := by
      exact ContMDiffAt.sum fun i _ => ContMDiffAt.sum fun j _ =>
        (hinv i j).mul (hA i j)
    exact (hs.congr_of_eventuallyEq heq).contMDiffWithinAt

end PoincareConjecture

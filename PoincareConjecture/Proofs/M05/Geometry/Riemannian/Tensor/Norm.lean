import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Tensor.Contraction
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
open Filter

namespace PoincareConjecture

section LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq σ]

private def linearProduct (L K : E →ₗ[ℝ] ℝ) : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => L u * K v)
    (by intros; simp [add_mul]) (by intros; simp [mul_assoc])
    (by intros; simp [mul_add]) (by intros; simp [mul_left_comm])

omit [DecidableEq κ] in
lemma sum_basis_repr_mul_eq_inverse_gram
    (b : Module.Basis ι ℝ E) (c : OrthonormalBasis κ ℝ E) (i j : ι) :
    (∑ a, b.repr (c a) i * b.repr (c a) j) =
      (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ i j := by
  let L : ι → E →ₗ[ℝ] ℝ := fun i => (Finsupp.lapply i).comp b.repr.toLinearMap
  have h := bilinear_sum_basis_eq_inverse_gram (linearProduct (L i) (L j)) b c
  simpa [linearProduct, L, Module.Basis.repr_self, Finsupp.single_apply] using h

omit [DecidableEq ι] in
lemma multilinear_apply_basis_expansion
    (A : MultilinearMap ℝ (fun _ : σ => E) ℝ) (b : Module.Basis ι ℝ E)
    (v : σ → E) :
    A v = ∑ i : σ → ι, (∏ r, b.repr (v r) (i r)) * A (fun r => b (i r)) := by
  have hv : v = fun r => ∑ i, b.repr (v r) i • b i :=
    funext fun r => (b.sum_repr (v r)).symm
  conv_lhs => rw [hv, A.map_sum]
  simp only [A.map_smul_univ, smul_eq_mul]

omit [DecidableEq κ] in

theorem multilinear_sum_mul_eq_inverse_gram
    (A B : MultilinearMap ℝ (fun _ : σ => E) ℝ)
    (b : Module.Basis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ a : σ → κ, A (fun r => c (a r)) * B (fun r => c (a r))) =
      ∑ i : σ → ι, ∑ j : σ → ι,
        (∏ r, (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ (i r) (j r)) *
          (A (fun r => b (i r)) * B (fun r => b (j r))) := by
  classical
  conv_lhs =>
    arg 2
    ext a
    rw [multilinear_apply_basis_expansion A b, multilinear_apply_basis_expansion B b]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hterm (a : σ → κ) :
      ((∏ r, b.repr (c (a r)) (i r)) * A (fun r => b (i r))) *
        ((∏ r, b.repr (c (a r)) (j r)) * B (fun r => b (j r))) =
      (∏ r, b.repr (c (a r)) (i r) * b.repr (c (a r)) (j r)) *
        (A (fun r => b (i r)) * B (fun r => b (j r))) := by
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_mul,
    ← Fintype.prod_sum (fun r a => b.repr (c a) (i r) * b.repr (c a) (j r))]
  simp_rw [sum_basis_repr_mul_eq_inverse_gram b c]

omit [DecidableEq ι] [DecidableEq κ] in

theorem multilinear_sum_mul_orthonormalBasis_eq
    (A B : MultilinearMap ℝ (fun _ : σ => E) ℝ)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ a : σ → ι, A (fun r => b (a r)) * B (fun r => b (a r))) =
      ∑ a : σ → κ, A (fun r => c (a r)) * B (fun r => c (a r)) := by
  classical
  exact (multilinear_sum_mul_eq_inverse_gram A B b.toBasis b).trans
    (multilinear_sum_mul_eq_inverse_gram A B b.toBasis c).symm

end LinearAlgebra

section Isometries

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ] [DecidableEq σ]

theorem multilinear_sum_sq_comp_linearIsometryEquiv
    (A : MultilinearMap ℝ (fun _ : σ => F) ℝ) (e : E ≃ₗᵢ[ℝ] F)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ F) :
    (∑ a : σ → ι, (A (fun r => e (b (a r)))) ^ 2) =
      ∑ a : σ → κ, (A (fun r => c (a r))) ^ 2 := by
  simpa only [pow_two, OrthonormalBasis.map_apply] using
    multilinear_sum_mul_orthonormalBasis_eq A A (b.map e) c

end Isometries

section Continuity

variable {ι σ α : Type*} [Fintype ι] [Fintype σ] [DecidableEq ι]
  [DecidableEq σ]

noncomputable def tensorNormFromComponents (G : Matrix ι ι ℝ)
    (R : (σ → ι) → ℝ) : ℝ :=
  Real.sqrt (∑ i : σ → ι, ∑ j : σ → ι,
    (∏ r, G⁻¹ (i r) (j r)) * (R i * R j))

theorem tendsto_tensorNormFromComponents {l : Filter α}
    {Gseq : α → Matrix ι ι ℝ} {G : Matrix ι ι ℝ}
    {Rseq : α → (σ → ι) → ℝ} {R : (σ → ι) → ℝ}
    (hG : ∀ i j, Tendsto (fun a => Gseq a i j) l (𝓝 (G i j)))
    (hR : ∀ i, Tendsto (fun a => Rseq a i) l (𝓝 (R i)))
    (hdet : G.det ≠ 0) :
    Tendsto (fun a => tensorNormFromComponents (Gseq a) (Rseq a)) l
      (𝓝 (tensorNormFromComponents G R)) := by
  have hmatrix : Tendsto Gseq l (𝓝 G) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hG i j
  have hinv : Tendsto (fun a => (Gseq a)⁻¹) l (𝓝 G⁻¹) := by
    apply (continuousAt_matrix_inv G ?_).tendsto.comp hmatrix
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [heq]
    exact continuousAt_inv₀ hdet
  have hentry (i j : ι) : Tendsto (fun a => (Gseq a)⁻¹ i j) l (𝓝 (G⁻¹ i j)) :=
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hinv i)) j
  unfold tensorNormFromComponents
  apply Real.continuous_sqrt.continuousAt.tendsto.comp
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (tendsto_finsetProd _ (fun r _ => hentry (i r) (j r))).mul ((hR i).mul (hR j))

end Continuity

theorem tensorNormFromComponents_eq_sqrt_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
    [DecidableEq ι] [DecidableEq σ]
    (A : MultilinearMap ℝ (fun _ : σ => E) ℝ)
    (b : Module.Basis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    tensorNormFromComponents (Matrix.of (fun i j => inner ℝ (b i) (b j)))
        (fun i : σ → ι => A (fun r => b (i r))) =
      Real.sqrt (∑ a : σ → κ, (A (fun r => c (a r))) ^ 2) := by
  unfold tensorNormFromComponents
  exact congrArg Real.sqrt (by
    simpa only [pow_two] using (multilinear_sum_mul_eq_inverse_gram A A b c).symm)

section VaryingMetrics

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def tensorHilbertSchmidtNorm (g : InnerProductSpace.Core ℝ E)
    (A : MultilinearMap ℝ (fun _ : σ => E) ℝ) : ℝ := by
  letI : NormedAddCommGroup E := g.toNormedAddCommGroup
  letI : InnerProductSpace ℝ E := InnerProductSpace.ofCore g.toCore
  exact Real.sqrt (∑ a : σ → Fin (Module.finrank ℝ E),
    (A (fun r => stdOrthonormalBasis ℝ E (a r))) ^ 2)

theorem tensorHilbertSchmidtNorm_eq_tensorNormFromComponents
    (g : InnerProductSpace.Core ℝ E)
    (A : MultilinearMap ℝ (fun _ : σ => E) ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    tensorHilbertSchmidtNorm g A =
      tensorNormFromComponents (Matrix.of (fun i j => g.inner (b i) (b j)))
        (fun i : σ → ι => A (fun r => b (i r))) := by
  let : NormedAddCommGroup E := g.toNormedAddCommGroup
  let : InnerProductSpace ℝ E := InnerProductSpace.ofCore g.toCore
  exact (tensorNormFromComponents_eq_sqrt_sum A b (stdOrthonormalBasis ℝ E)).symm

theorem tendsto_tensorHilbertSchmidtNorm
    {α : Type*} {l : Filter α}
    {gseq : α → InnerProductSpace.Core ℝ E} {g : InnerProductSpace.Core ℝ E}
    {Aseq : α → MultilinearMap ℝ (fun _ : σ => E) ℝ}
    {A : MultilinearMap ℝ (fun _ : σ => E) ℝ}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    (hG : ∀ i j, Tendsto (fun a => (gseq a).inner (b i) (b j)) l
      (𝓝 (g.inner (b i) (b j))))
    (hA : ∀ i : σ → ι, Tendsto (fun a => Aseq a (fun r => b (i r))) l
      (𝓝 (A (fun r => b (i r))))) :
    Tendsto (fun a => tensorHilbertSchmidtNorm (gseq a) (Aseq a)) l
      (𝓝 (tensorHilbertSchmidtNorm g A)) := by
  let : NormedAddCommGroup E := g.toNormedAddCommGroup
  let : InnerProductSpace ℝ E := InnerProductSpace.ofCore g.toCore
  have hdet : (Matrix.of (fun i j => g.inner (b i) (b j))).det ≠ 0 := by
    change (Matrix.gram ℝ b).det ≠ 0
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr b.linearIndependent
  simp_rw [tensorHilbertSchmidtNorm_eq_tensorNormFromComponents _ _ b]
  exact tendsto_tensorNormFromComponents hG hA hdet

end VaryingMetrics

end PoincareConjecture

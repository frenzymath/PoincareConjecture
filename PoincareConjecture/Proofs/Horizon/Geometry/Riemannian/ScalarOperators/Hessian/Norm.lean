import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Bochner
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.TraceRegularity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiff_hessian_normSq (D : LeviCivitaData g)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x =>
      ∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) := by
  let T : CovariantTensorEvaluation n M 2 := fun x v =>
    g.inner x (D.connection (D.gradient f) x (v 0))
      (D.connection (D.gradient f) x (v 1))
  have hT : IsSmoothCovariantTensor T := by
    constructor
    · intro x
      let A : MultilinearMap ℝ (fun _ : Fin 2 => TangentSpace (𝓡 n) x) ℝ :=
        { toFun := T x
          map_update_add' := by
            intro _ v i a b
            fin_cases i <;> simp [T, map_add]
          map_update_smul' := by
            intro _ v i c a
            fin_cases i <;> simp [T, map_smul, smul_eq_mul] }
      exact ⟨A, fun _ => rfl⟩
    · intro U hU X hX
      have hgrad := D.contMDiff_gradient hf
      have hconnection := D.smooth.contMDiff.contMDiff
        (show ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (∞ + 1) (T% (D.gradient f)) Set.univ from by simpa using hgrad.contMDiffOn)
      have hc (i : Fin 2) :=
        (contMDiffOn_univ.mp hconnection).contMDiffOn.clm_bundle_apply (hX i)
      have hi := (g.contMDiff.contMDiffOn.clm_bundle_apply (hc 0)).clm_bundle_apply (hc 1)
      intro x hx
      have hs := (Bundle.contMDiffAt_totalSpace.mp
        ((hi x hx).contMDiffAt (hU.mem_nhds hx))).2
      exact hs.contMDiffWithinAt
  have htrace := hT.tensorTrace (g := g) (k := 0)
  have h := htrace.2 Set.univ isOpen_univ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  simp only [contMDiffOn_univ, RiemannianMetric.tensorTrace, T, Fin.cons_zero,
    Fin.cons_one] at h
  simpa only [D.sum_hessian_sq_eq_inner_connection_gradient (hf _)] using h

private theorem abs_inner_linearMap_self_le_hilbert
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (L : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) (v : E) :
    |⟪L v, v⟫_ℝ| ≤
      Real.sqrt (∑ i, ⟪L (b i), L (b i)⟫_ℝ) * ⟪v, v⟫_ℝ := by
  have hexp : ⟪L v, v⟫_ℝ = ∑ i, ⟪b i, v⟫_ℝ * ⟪L (b i), v⟫_ℝ := by
    have h := congrArg (fun w => ⟪L w, v⟫_ℝ) (b.sum_repr' v)
    simpa only [map_sum, map_smul, sum_inner, real_inner_smul_left] using h.symm
  have hparseval : (∑ i, ⟪b i, v⟫_ℝ ^ 2) = ⟪v, v⟫_ℝ := by
    simpa only [Real.norm_eq_abs, sq_abs, real_inner_self_eq_norm_sq] using
      b.sum_sq_norm_inner_right v
  have hupper : (∑ i, ⟪L (b i), v⟫_ℝ ^ 2) ≤
      (∑ i, ⟪L (b i), L (b i)⟫_ℝ) * ⟪v, v⟫_ℝ := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    simpa only [← pow_two] using real_inner_mul_inner_self_le (L (b i)) v
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ⟪b i, v⟫_ℝ) (fun i => ⟪L (b i), v⟫_ℝ)
  rw [← hexp, hparseval] at hcs
  have hbound := hcs.trans (mul_le_mul_of_nonneg_left hupper real_inner_self_nonneg)
  have hsum : 0 ≤ ∑ i, ⟪L (b i), L (b i)⟫_ℝ :=
    Finset.sum_nonneg fun _ _ => real_inner_self_nonneg
  have hsqrt := Real.sq_sqrt hsum
  have hnonneg : 0 ≤ Real.sqrt (∑ i, ⟪L (b i), L (b i)⟫_ℝ) * ⟪v, v⟫_ℝ :=
    mul_nonneg (Real.sqrt_nonneg _) real_inner_self_nonneg
  apply (sq_le_sq₀ (abs_nonneg _) hnonneg).mp
  rw [sq_abs, mul_pow, hsqrt]
  nlinarith only [hbound]

theorem abs_hessian_quadratic_le_normSq (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (v : TangentSpace (𝓡 n) x) :
    |D.hessian f x v v| ≤
      Real.sqrt (∑ i, ∑ j, (D.hessian f x
        (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) * g.inner x v v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp_rw [D.sum_hessian_sq_eq_inner_connection_gradient hf]
  rw [D.hessian_eq_inner_connection_gradient hf]
  exact abs_inner_linearMap_self_le_hilbert (D.connection (D.gradient f) x)
    (g.orthonormalBasis x) v

end PoincareConjecture.LeviCivitaData

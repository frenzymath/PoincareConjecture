import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralBasis
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralSmoothing











set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology InnerProductSpace NNReal

namespace Poincare.Analysis.Dirichlet.CompactSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem finite_eigenvalue_modulus_ge (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {i : BasisIndex T | ε ≤ |i.1.1|} := by
  classical
  by_contra hinfinite
  rw [Set.not_finite] at hinfinite
  let f : ℕ ↪ {i : BasisIndex T | ε ≤ |i.1.1|} := hinfinite.natEmbedding
  let b := basisVector T hT
  have hb : Orthonormal ℝ b := basisVector_orthonormal T hT hself
  have heig (i : BasisIndex T) : T (b i) = i.1.1 • b i :=
    Module.End.mem_eigenspace_iff.mp (basisVector_mem T hT i)
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact (1 : ℝ)
  have hmem (n : ℕ) : T (b (f n)) ∈ K :=
    hTK ⟨b (f n), by simp [Metric.mem_closedBall, dist_zero_right, hb.1], rfl⟩
  obtain ⟨y, hy, ψ, hψ, hlim⟩ := hK.tendsto_subseq hmem
  have hcauchy := hlim.cauchySeq
  rw [Metric.cauchySeq_iff'] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy ε hε
  have hclose := hN (N + 1) (Nat.le_succ N)
  have hne : (f (ψ (N + 1)) : BasisIndex T) ≠ f (ψ N) := by
    intro heq
    exact (Nat.ne_of_gt (hψ (Nat.lt_succ_self N)))
      (f.injective (Subtype.ext heq))
  have hinner :
      ⟪T (b (f (ψ (N + 1)))) - T (b (f (ψ N))), b (f (ψ (N + 1)))⟫_ℝ =
        (f (ψ (N + 1))).1.1.1 := by
    rw [inner_sub_left, heig, heig, real_inner_smul_left, real_inner_smul_left,
      hb.inner_eq_zero hne.symm, mul_zero, sub_zero,
      real_inner_self_eq_norm_sq, hb.1, one_pow, mul_one]
  have hfar : ε ≤ ‖T (b (f (ψ (N + 1)))) - T (b (f (ψ N)))‖ := by
    calc
      ε ≤ |(f (ψ (N + 1))).1.1.1| := (f (ψ (N + 1))).property
      _ = |⟪T (b (f (ψ (N + 1)))) - T (b (f (ψ N))), b (f (ψ (N + 1)))⟫_ℝ| :=
        congrArg abs hinner.symm
      _ ≤ ‖T (b (f (ψ (N + 1)))) - T (b (f (ψ N)))‖ * ‖b (f (ψ (N + 1)))‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖T (b (f (ψ (N + 1)))) - T (b (f (ψ N)))‖ := by rw [hb.1, mul_one]
  rw [dist_eq_norm] at hclose
  exact (not_lt_of_ge hfar) hclose

theorem countable_basisIndex (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) : Countable (BasisIndex T) := by
  have hcover : (Set.univ : Set (BasisIndex T)) =
      ⋃ n : ℕ, {i : BasisIndex T | 1 / (n + 1 : ℝ) ≤ |i.1.1|} := by
    ext i
    simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_ofPred_eq, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr i.1.2.1)
    exact ⟨n, hn.le⟩
  apply Set.countable_univ_iff.mp
  rw [hcover]
  exact Set.countable_iUnion fun n =>
    (finite_eigenvalue_modulus_ge T hT hself (ε := 1 / (n + 1)) (by positivity)).countable

theorem finite_eigenvalue_ge (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) {ε : ℝ} (hε : 0 < ε) :
    Set.Finite {i : BasisIndex T | ε ≤ i.1.1} :=
  (finite_eigenvalue_modulus_ge T hT hself hε).subset
    (fun i hi => (show ε ≤ i.1.1 from hi).trans (le_abs_self _))

omit [CompleteSpace H] in
theorem nonzeroEigenvalue_pos (T : H →L[ℝ] H)
    (hpositive : ∀ u : H, 0 ≤ ⟪T u, u⟫_ℝ) (μ : NonzeroEigenvalue T) : 0 < μ.1 := by
  have hnonneg : 0 ≤ μ.1 := eigenvalue_nonneg_of_nonneg μ.2.2 (fun u => by
    change 0 ≤ ⟪u, T u⟫_ℝ
    rw [real_inner_comm]
    exact hpositive u)
  exact lt_of_le_of_ne hnonneg (Ne.symm μ.2.1)

theorem finite_transformed_rate_le (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) (hpos : ∀ i : BasisIndex T, 0 < i.1.1)
    {R : ℝ} (hR : 0 ≤ R) :
    Set.Finite {i : BasisIndex T | (1 - i.1.1) / i.1.1 ≤ R} := by
  apply (finite_eigenvalue_ge T hT hself (ε := 1 / (R + 1)) (by positivity)).subset
  intro i hi
  have hmul := (div_le_iff₀ (hpos i)).mp hi
  apply (div_le_iff₀ (by positivity : 0 < R + 1)).mpr
  nlinarith

theorem finite_transformed_rate_le_of_nonneg (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hself : IsSelfAdjoint T) (hpositive : ∀ u : H, 0 ≤ ⟪T u, u⟫_ℝ)
    {R : ℝ} (hR : 0 ≤ R) :
    Set.Finite {i : BasisIndex T | (1 - i.1.1) / i.1.1 ≤ R} :=
  finite_transformed_rate_le T hT hself (fun i => nonzeroEigenvalue_pos T hpositive i.1) hR

end Poincare.Analysis.Dirichlet.CompactSpectral

namespace Poincare.Analysis.Dirichlet.Spectral

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem heat_eq_resolvent_comp (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0)
    (T : H →L[ℝ] H) (hdiag : ∀ i, T (b i) = (1 + (lam i : ℝ))⁻¹ • b i)
    {t : ℝ} (ht : 0 < t) :
    heat b lam t.toNNReal = T.comp (heatPower b lam 0 t + heatPower b lam 1 t) := by
  ext u
  let v := heatPower b lam 0 t u + heatPower b lam 1 t u
  have hsum := (b.hasSum_repr v).mapL T
  have hcoef (i : ι) : b.repr v i * (1 + (lam i : ℝ))⁻¹ =
      Real.exp (-(lam i : ℝ) * t) * b.repr u i := by
    dsimp [v]
    simp only [map_add, lp.coeFn_add, Pi.add_apply, heatPower_repr b lam 0 ht,
      heatPower_repr b lam 1 ht, pow_zero, pow_one, one_mul]
    have hn : (1 + (lam i : ℝ)) ≠ 0 := by positivity
    field_simp
  have hsum' : HasSum
      (fun i => (Real.exp (-(lam i : ℝ) * t) * b.repr u i) • b i) (T v) := by
    convert hsum using 1
    funext i
    rw [map_smul, hdiag, smul_smul, hcoef]
  have hheat : HasSum
      (fun i => (Real.exp (-(lam i : ℝ) * t) * b.repr u i) • b i)
      (heat b lam t.toNNReal u) := by
    simpa [Real.coe_toNNReal _ ht.le] using heat_hasSum b lam t.toNNReal u
  exact hheat.unique hsum'

theorem isCompactOperator_heat_of_resolvent (b : HilbertBasis ι ℝ H) (lam : ι → ℝ≥0)
    (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (hdiag : ∀ i, T (b i) = (1 + (lam i : ℝ))⁻¹ • b i)
    {t : ℝ} (ht : 0 < t) : IsCompactOperator (heat b lam t.toNNReal) := by
  rw [heat_eq_resolvent_comp b lam T hdiag ht]
  exact hT.comp_clm (heatPower b lam 0 t + heatPower b lam 1 t)

end Poincare.Analysis.Dirichlet.Spectral

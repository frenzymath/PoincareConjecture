import PoincareConjecture.Proofs.M03.CompactFiniteCoefficient

set_option autoImplicit false

open Set
open scoped BigOperators

theorem LinearMap.apply_eq_sum_equiv_coordinates
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommMonoid F] [Module ℝ F] {d : ℕ}
    (L : E →ₗ[ℝ] F) (q : E ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (x : E) :
    L x = ∑ i : Fin d, q x i • L (q.symm (EuclideanSpace.single i 1)) := by
  let b := PiLp.basisFun 2 ℝ (Fin d)
  have hv : q x = ∑ i : Fin d, q x i • EuclideanSpace.single i 1 := by
    simpa [b, PiLp.basisFun_repr, PiLp.basisFun_apply] using (b.sum_repr (q x)).symm
  have hx : x = ∑ i : Fin d, q x i • q.symm (EuclideanSpace.single i 1) := by
    calc
      x = q.symm (q x) := (q.symm_apply_apply x).symm
      _ = q.symm (∑ i : Fin d, q x i • EuclideanSpace.single i 1) := congrArg q.symm hv
      _ = _ := by simp only [map_sum, map_smul]
  calc
    L x = L (∑ i : Fin d, q x i • q.symm (EuclideanSpace.single i 1)) := congrArg L hx
    _ = _ := by simp only [map_sum, map_smul]

theorem exists_compact_three_linear_coordinate_bound
    {X I H A S : Type*} [TopologicalSpace X] [Fintype I]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    {dH dA dS : ℕ} {K : Set X} (hK : IsCompact K)
    (qH : H ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : A ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : S ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (LH : X → H →ₗ[ℝ] (I → ℝ)) (LA : X → A →ₗ[ℝ] (I → ℝ))
    (LS : X → S →ₗ[ℝ] (I → ℝ))
    (hLH : ∀ h i, ContinuousOn (fun p => LH p h i) K)
    (hLA : ∀ a i, ContinuousOn (fun p => LA p a i) K)
    (hLS : ∀ s i, ContinuousOn (fun p => LS p s i) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ h a s,
      let density := (∑ j, qH h j ^ 2) + (∑ j, qA a j ^ 2) + (∑ j, qS s j ^ 2)
      (∑ i, (LH p h i + LA p a i + LS p s i) ^ 2) ≤ C * density ∧
      ∀ ε : ℝ, 0 < ε → ∀ alpha : I → ℝ,
        (∑ i, 2 * alpha i * (LH p h i + LA p a i + LS p s i)) ≤
          ε * density + (C / ε) * ∑ i, alpha i ^ 2 := by
  classical
  let c : X → I → (Fin dH ⊕ (Fin dA ⊕ Fin dS)) → ℝ := fun p i =>
    Sum.elim (fun j => LH p (qH.symm (EuclideanSpace.single j 1)) i)
      (Sum.elim (fun j => LA p (qA.symm (EuclideanSpace.single j 1)) i)
        (fun j => LS p (qS.symm (EuclideanSpace.single j 1)) i))
  have hc (i : I) (j : Fin dH ⊕ (Fin dA ⊕ Fin dS)) :
      ContinuousOn (fun p => c p i j) K := by
    rcases j with j | j | j
    · exact hLH _ i
    · exact hLA _ i
    · exact hLS _ i
  obtain ⟨C, hC, hbound⟩ := PoincareConjecture.Proofs.M03.exists_compact_finite_square_sum_bound hK c hc
  refine ⟨C, hC, fun p hp h a s => ?_⟩
  let values : Fin dH ⊕ (Fin dA ⊕ Fin dS) → ℝ :=
    Sum.elim (fun j => qH h j) (Sum.elim (fun j => qA a j) (fun j => qS s j))
  have hvalues : (∑ j, values j ^ 2) =
      (∑ j, qH h j ^ 2) + (∑ j, qA a j ^ 2) + (∑ j, qS s j ^ 2) := by
    simp only [values, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, add_assoc]
  have hrepr (i : I) : LH p h i + LA p a i + LS p s i = ∑ j, c p i j * values j := by
    have hh := ((LinearMap.proj i).comp (LH p)).apply_eq_sum_equiv_coordinates qH h
    have ha := ((LinearMap.proj i).comp (LA p)).apply_eq_sum_equiv_coordinates qA a
    have hs := ((LinearMap.proj i).comp (LS p)).apply_eq_sum_equiv_coordinates qS s
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul] at hh ha hs
    rw [hh, ha, hs]
    simp only [c, values, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      add_assoc, mul_comm]
  constructor
  · have hsq := (PoincareConjecture.Proofs.M03.sum_sq_linear_combination_le (c p) values).trans
      (mul_le_mul_of_nonneg_right (hbound p hp) (by positivity))
    simpa only [← hrepr, hvalues] using hsq
  · intro ε hε alpha
    have hpair := PoincareConjecture.Proofs.M03.sum_two_mul_linear_combination_le
      (c p) alpha values hε (hbound p hp) hC
    simpa only [← hrepr, hvalues] using hpair

theorem exists_compact_finite_linear_coordinate_bound
    {X I B : Type*} [TopologicalSpace X] [Fintype I] [Fintype B]
    {K : Set X} (hK : IsCompact K) (L : X → (B → ℝ) →ₗ[ℝ] (I → ℝ))
    (hL : ∀ v i, ContinuousOn (fun p => L p v i) K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ v : B → ℝ,
      (∑ i, L p v i ^ 2) ≤ C * (∑ b, v b ^ 2) ∧
      ∀ ε : ℝ, 0 < ε → ∀ alpha : I → ℝ,
        (∑ i, 2 * alpha i * L p v i) ≤
          ε * (∑ b, v b ^ 2) + (C / ε) * ∑ i, alpha i ^ 2 := by
  classical
  let c : X → I → B → ℝ := fun p i b => L p (Pi.single b 1) i
  obtain ⟨C, hC, hbound⟩ := PoincareConjecture.Proofs.M03.exists_compact_finite_square_sum_bound
    hK c (fun i b => hL (Pi.single b 1) i)
  refine ⟨C, hC, fun p hp v => ?_⟩
  have hv : v = ∑ b : B, v b • Pi.single b (1 : ℝ) := by
    ext b
    simp [Pi.single_apply]
  have hrepr (i : I) : L p v i = ∑ b, c p i b * v b := by
    calc
      L p v i = L p (∑ b : B, v b • Pi.single b (1 : ℝ)) i := congrArg (fun w => L p w i) hv
      _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, c, mul_comm]
  constructor
  · have hsq := (PoincareConjecture.Proofs.M03.sum_sq_linear_combination_le (c p) v).trans
      (mul_le_mul_of_nonneg_right (hbound p hp) (by positivity))
    simpa only [← hrepr] using hsq
  · intro ε hε alpha
    have hpair := PoincareConjecture.Proofs.M03.sum_two_mul_linear_combination_le
      (c p) alpha v hε (hbound p hp) hC
    simpa only [← hrepr] using hpair

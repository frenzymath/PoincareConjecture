import PoincareConjecture.Proofs.M04.ConnectionVariationVector

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

set_option backward.isDefEq.respectTransparency false in
private theorem hasDerivAt_multilinear_update
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {k : ℕ} (A : ℝ → MultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ)
    {S : (Fin k → E) → ℝ} {t : ℝ}
    (hA : ∀ w, HasDerivAt (fun s ↦ A s w) (S w) t)
    {c : ℝ → E} {c' : E} (hc : HasDerivAt c c' t)
    (v : Fin k → E) (i : Fin k) :
    HasDerivAt (fun s ↦ A s (Function.update v i (c s)))
      (S (Function.update v i (c t)) +
        A t (Function.update v i c')) t := by
  classical
  have hExpand (s : ℝ) (z : E) :
      A s (Function.update v i z) =
        ∑ q, inner ℝ (b q) z * A s (Function.update v i (b q)) := by
    conv_lhs => rw [← b.sum_repr' z]
    rw [(A s).map_update_sum]
    simp only [MultilinearMap.map_update_smul, smul_eq_mul]
  have hFrozen := HasDerivAt.fun_sum (u := Finset.univ)
    (fun q _ ↦ (hA (Function.update v i (b q))).const_mul (inner ℝ (b q) (c t)))
  have hS : S (Function.update v i (c t)) =
      ∑ q, inner ℝ (b q) (c t) * S (Function.update v i (b q)) :=
    (hA (Function.update v i (c t))).unique
      (hFrozen.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ hExpand s (c t)))
  have hInner (q : ι) :
      HasDerivAt (fun s ↦ inner ℝ (b q) (c s)) (inner ℝ (b q) c') t := by
    simpa only [Function.comp_def, innerSL_apply_apply] using!
      (innerSL ℝ (b q)).hasFDerivAt.comp_hasDerivAt t hc
  have hMoving := HasDerivAt.fun_sum (u := Finset.univ)
    (fun q _ ↦ (hInner q).mul (hA (Function.update v i (b q))))
  have hValue :
      (∑ q, (inner ℝ (b q) c' * A t (Function.update v i (b q)) +
        inner ℝ (b q) (c t) * S (Function.update v i (b q)))) =
      S (Function.update v i (c t)) + A t (Function.update v i c') := by
    rw [Finset.sum_add_distrib, ← hExpand t c', ← hS, add_comm]
  exact (hMoving.congr_deriv hValue).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ hExpand s (c s))

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_covariantTensorDerivative (F : RicciFlow n M J)
    {k : ℕ} {T : ℝ → CovariantTensorEvaluation n M k}
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hJoint : ∀ (U : Set M), IsOpen U →
      ∀ (X : Fin k → (y : M) → TangentSpace (𝓡 n) y),
        (∀ i, ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (X i)) U) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ T p.1 p.2 (fun i ↦ X i p.2))
          (J ×ˢ U))
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (a : TangentSpace (𝓡 n) x)
    (v : Fin k → TangentSpace (𝓡 n) x) :
    let D := F.connection t
    let b := (F.metric t).orthonormalBasis x
    let S : CovariantTensorEvaluation n M k :=
      fun y w ↦ deriv (fun s ↦ T s y w) t
    HasDerivAt
      (fun s ↦ (F.connection s).covariantTensorDerivative (T s)
        x (Fin.cons a v))
      (D.covariantTensorDerivative S x (Fin.cons a v) +
        ∑ i, ∑ q,
          (D.covariantTensorDerivative D.ricciEvaluation x ![a, v i, b q] +
            D.covariantTensorDerivative D.ricciEvaluation x ![v i, a, b q] -
            D.covariantTensorDerivative D.ricciEvaluation x ![b q, a, v i]) *
          T t x (Function.update v i (b q))) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let D := F.connection t
  let b := (F.metric t).orthonormalBasis x
  let S : CovariantTensorEvaluation n M k :=
    fun y w ↦ deriv (fun s ↦ T s y w) t
  let B (i : Fin k) (q : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :=
    D.covariantTensorDerivative D.ricciEvaluation x ![a, v i, b q] +
      D.covariantTensorDerivative D.ricciEvaluation x ![v i, a, b q] -
      D.covariantTensorDerivative D.ricciEvaluation x ![b q, a, v i]
  change HasDerivAt
    (fun s ↦ (F.connection s).covariantTensorDerivative (T s) x (Fin.cons a v))
    (D.covariantTensorDerivative S x (Fin.cons a v) +
      ∑ i, ∑ q, B i q * T t x (Function.update v i (b q))) t
  have hTime (y : M) (w : Fin k → TangentSpace (𝓡 n) y) :
      HasDerivAt (fun s ↦ T s y w) (S y w) t := by
    let e := trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) y
    let W := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (w i)
    have hW (i : Fin k) : ContMDiffOn (𝓡 n)
        ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (W i)) e.baseSet :=
      contMDiffOn_extend_baseSet (w i)
    have hEmbed : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
        (fun s : ℝ ↦ (s, y)) J := contMDiffOn_id.prodMk contMDiffOn_const
    have hSlice := (hJoint e.baseSet e.open_baseSet W hW).comp hEmbed
      (show MapsTo (fun s : ℝ ↦ (s, y)) J (J ×ˢ e.baseSet) from
        fun _ hs ↦ ⟨hs, FiberBundle.mem_baseSet_trivializationAt' y⟩)
    have hSmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s ↦ T s y w) J := by
      apply hSlice.congr
      intro s _
      change T s y w = T s y (fun i ↦ W i y)
      simp only [W, FiberBundle.extend_apply_self]
    exact ((hSmooth.contMDiffAt (mem_interior_iff_mem_nhds.mp ht)).contDiffAt
      |>.differentiableAt (by simp)).hasDerivAt
  let e := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type _) x
  let X := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) a
  let V := fun i ↦ FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (v i)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hX : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) e.baseSet :=
    contMDiffOn_extend_baseSet a
  have hV (i : Fin k) : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% (V i)) e.baseSet :=
    contMDiffOn_extend_baseSet (v i)
  have hLeading := hasDerivAt_mvfderiv_time e.open_baseSet
    (hJoint e.baseSet e.open_baseSet V hV) ht hx
    (fun y _ ↦ hTime y (fun i ↦ V i y)) a
  let C (i : Fin k) (s : ℝ) := (F.connection s).connection (V i) x a
  let C' (i : Fin k) := ∑ q, (-B i q) • b q
  have hConnection (i : Fin k) : HasDerivAt (C i) (C' i) t := by
    have h := hasDerivAt_connection_vector F e.open_baseSet hX (hV i) ht hx
    simp only [X, V, FiberBundle.extend_apply_self] at h
    apply h.congr_deriv
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    dsimp only [B, D, b]
    ring
  choose A hA using fun s ↦ (hT s).1 x
  have hATime (w : Fin k → TangentSpace (𝓡 n) x) :
      HasDerivAt (fun s ↦ A s w) (S x w) t :=
    (hTime x w).congr_of_eventuallyEq
      (Eventually.of_forall fun s ↦ (hA s w).symm)
  have hCorrection (i : Fin k) :
      HasDerivAt (fun s ↦ T s x (Function.update v i (C i s)))
        (S x (Function.update v i (C i t)) +
          T t x (Function.update v i (C' i))) t := by
    have h := hasDerivAt_multilinear_update b A hATime (hConnection i) v i
    simpa only [← hA] using h
  have hCorrectionValue (i : Fin k) :
      T t x (Function.update v i (C' i)) =
        -(∑ q, B i q * T t x (Function.update v i (b q))) := by
    rw [hA, show C' i = ∑ q, (-B i q) • b q from rfl,
      (A t).map_update_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [(A t).map_update_smul, hA]
    simp only [smul_eq_mul, neg_mul]
  have hSum :
      (∑ i, T t x (Function.update v i (C' i))) =
        -(∑ i, ∑ q, B i q * T t x (Function.update v i (b q))) := by
    simp_rw [hCorrectionValue]
    rw [Finset.sum_neg_distrib]
  have hValue :
      mvfderiv (𝓡 n) (fun y ↦ S y (fun i ↦ V i y)) x a -
        ∑ i, (S x (Function.update v i (C i t)) +
          T t x (Function.update v i (C' i))) =
      D.covariantTensorDerivative S x (Fin.cons a v) +
        ∑ i, ∑ q, B i q * T t x (Function.update v i (b q)) := by
    rw [Finset.sum_add_distrib, hSum]
    simp only [LeviCivitaData.covariantTensorDerivative, Fin.cons_zero, Fin.cons_succ]
    dsimp only [C, V, D]
    ring
  have h := hLeading.sub (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ ↦ hCorrection i))
  exact h.congr_deriv hValue

end PoincareConjecture.M04

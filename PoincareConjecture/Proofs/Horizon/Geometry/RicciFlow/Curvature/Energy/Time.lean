import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Energy.Regularity
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations












set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem frameGramOperator_pairing
    (g : RiemannianMetric n M) (x : M)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) x)
    (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (frameGramOperator g x L v) w = g.inner x (L v) (L w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (((g.inner x).bilinearComp L L) v)) w = _
  exact InnerProductSpace.toDual_symm_apply

private theorem frameGramOperator_expansion
    (g : RiemannianMetric n M) (x : M)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) x) :
    let b0 := EuclideanSpace.basisFun (Fin n) ℝ
    frameGramOperator g x L =
      ∑ i : Fin n, ∑ j : Fin n,
        g.inner x (L (b0 i)) (L (b0 j)) •
          InnerProductSpace.rankOne ℝ (b0 i) (b0 j) := by
  classical
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  apply ContinuousLinearMap.ext
  intro v
  have hcoeff (i : Fin n) :
      inner ℝ (b0 i) (frameGramOperator g x L v) =
        ∑ j, g.inner x (L (b0 i)) (L (b0 j)) * inner ℝ (b0 j) v := by
    rw [real_inner_comm, frameGramOperator_pairing, g.symm]
    calc
      _ = g.inner x (L (b0 i)) (L (∑ j, inner ℝ (b0 j) v • b0 j)) := by
        rw [b0.sum_repr']
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  calc
    _ = ∑ i, inner ℝ (b0 i) (frameGramOperator g x L v) • b0 i :=
      (b0.sum_repr' _).symm
    _ = ∑ i, (∑ j, g.inner x (L (b0 i)) (L (b0 j)) * inner ℝ (b0 j) v) • b0 i := by
      simp only [hcoeff]
    _ = _ := by
      simp only [sum_apply, smul_apply, InnerProductSpace.rankOne_apply,
        Finset.sum_smul, smul_smul, b0]

private theorem frameGramOperator_eq_id_of_orthonormal
    (g : RiemannianMetric n M) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (hON : ∀ i j : Fin n,
      g.inner x (e (EuclideanSpace.basisFun (Fin n) ℝ i))
          (e (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        if i = j then (1 : ℝ) else 0) :
    frameGramOperator g x e.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  classical
  rw [frameGramOperator_expansion]
  apply ContinuousLinearMap.ext
  intro v
  simp only [sum_apply, smul_apply, InnerProductSpace.rankOne_apply,
    ContinuousLinearEquiv.coe_coe, hON, ContinuousLinearMap.id_apply]
  simpa only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr' v

private theorem hasDerivAt_flow_frameGramOperator
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x) :
    let b0 := EuclideanSpace.basisFun (Fin n) ℝ
    HasDerivAt
      (fun s ↦ frameGramOperator (F.metric s) x e.toContinuousLinearMap)
      (∑ i : Fin n, ∑ j : Fin n,
        (-2 * (F.connection t).ricci x (e (b0 i)) (e (b0 j))) •
          InnerProductSpace.rankOne ℝ (b0 i) (b0 j)) t := by
  classical
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦
      ((F.equation t (interior_subset ht) x (e (b0 i)) (e (b0 j))).hasDerivAt
        (mem_interior_iff_mem_nhds.mp ht)).smul_const
          (InnerProductSpace.rankOne ℝ (b0 i) (b0 j))))
  simpa only [frameGramOperator_expansion, ContinuousLinearEquiv.coe_coe, b0] using h

private theorem hasDerivAt_inverse_at_identity
    (A : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {A' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {t : ℝ} (hA : HasDerivAt A A' t)
    (hAt : A t = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    (hInv : ∀ s, (A s).IsInvertible) :
    HasDerivAt (fun s ↦ (A s).inverse) (-A') t := by
  let E := EuclideanSpace ℝ (Fin n)
  let K : ℝ → E →L[ℝ] E := fun s ↦ (A s).inverse
  have hKd : DifferentiableAt ℝ K t :=
    (((hInv t).contDiffAt_map_inverse (n := 1)).differentiableAt (by norm_num)).comp
      t hA.differentiableAt
  have hKt : K t = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    have h := (hInv t).self_apply_inverse v
    change A t (K t v) = v at h
    simpa only [hAt, ContinuousLinearMap.id_apply] using h
  have hprod : (fun s ↦ (A s).comp (K s)) = fun _ ↦ ContinuousLinearMap.id ℝ E := by
    funext s
    apply ContinuousLinearMap.ext
    intro v
    exact (hInv s).self_apply_inverse v
  have hd := hA.clm_comp (E := E) (F := E) (G := E) hKd.hasDerivAt
  rw [hprod] at hd
  have hz := hd.unique (hasDerivAt_const t (ContinuousLinearMap.id ℝ E))
  rw [hAt, hKt, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp] at hz
  have hderiv : deriv K t = -A' := eq_neg_of_add_eq_zero_right hz
  exact hKd.hasDerivAt.congr_deriv hderiv

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_flow_frameInverseGram
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (hON : ∀ i j : Fin n,
      (F.metric t).inner x (e (EuclideanSpace.basisFun (Fin n) ℝ i))
          (e (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        if i = j then (1 : ℝ) else 0)
    (i j : Fin n) :
    let b0 := EuclideanSpace.basisFun (Fin n) ℝ
    HasDerivAt
      (fun s ↦ frameInverseGram (F.metric s) x e.toContinuousLinearMap i j)
      (2 * (F.connection t).ricci x (e (b0 i)) (e (b0 j))) t := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let A : ℝ → E →L[ℝ] E := fun s ↦ frameGramOperator (F.metric s) x e.toContinuousLinearMap
  have hAt : A t = ContinuousLinearMap.id ℝ E :=
    frameGramOperator_eq_id_of_orthonormal (F.metric t) x e hON
  have h := hasDerivAt_inverse_at_identity A
    (hasDerivAt_flow_frameGramOperator F ht x e) hAt
    (fun s ↦ frameGramOperator_isInvertible (F.metric s) x e)
  have he := (hasDerivAt_const t (innerSL ℝ (b0 i))).clm_apply (F := E) (G := ℝ)
    (h.clm_apply (F := E) (G := E) (hasDerivAt_const t (b0 j)))
  have he' : HasDerivAt
      (fun s ↦ frameInverseGram (F.metric s) x e.toContinuousLinearMap i j)
      (inner ℝ (b0 i) ((-∑ k : Fin n, ∑ l : Fin n,
        (-2 * (F.connection t).ricci x (e (b0 k)) (e (b0 l))) •
          InnerProductSpace.rankOne ℝ (b0 k) (b0 l)) (b0 j))) t := by
    convert! he using 1
    simp only [zero_apply, zero_add, map_zero, add_zero]
    rfl
  apply he'.congr_deriv
  simp only [neg_apply, sum_apply, smul_apply, InnerProductSpace.rankOne_apply, inner_neg_right,
    inner_sum, inner_smul_right, b0.inner_eq_ite]
  simp [b0]

private theorem kronecker_product_eq {r n : ℕ}
    (a b : Fin r → Fin n) :
    (∏ j : Fin r, if a j = b j then (1 : ℝ) else 0) =
      if a = b then (1 : ℝ) else 0 := by
  classical
  have he : (∀ j, a j = b j) ↔ a = b := ⟨funext, fun h j ↦ congrFun h j⟩
  rw [Fintype.prod_boole]
  simp only [he]

private theorem kronecker_product_erase_eq {r n : ℕ}
    (a b : Fin r → Fin n) (j : Fin r) :
    (∏ k ∈ Finset.univ.erase j, if a k = b k then (1 : ℝ) else 0) =
      if (∀ k : Fin r, k ≠ j → a k = b k) then (1 : ℝ) else 0 := by
  classical
  rw [Finset.prod_boole]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]

private theorem piSplitAt_symm_eq_update {r n : ℕ}
    (a : Fin r → Fin n) (j : Fin r) (l : Fin n) :
    (Equiv.piSplitAt j (fun _ : Fin r ↦ Fin n)).symm
        (l, fun k : {k : Fin r // k ≠ j} ↦ a k) =
      Function.update a j l := by
  funext k
  by_cases hk : k = j
  · subst k
    simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, hk]

private theorem sum_mul_kronecker_product {r n : ℕ}
    (a : Fin r → Fin n) (Q : (Fin r → Fin n) → ℝ) :
    (∑ b : Fin r → Fin n,
      Q b * ∏ j : Fin r, if a j = b j then (1 : ℝ) else 0) = Q a := by
  classical
  simp [kronecker_product_eq]

private theorem sum_mul_kronecker_product_erase {r n : ℕ}
    (a : Fin r → Fin n) (j : Fin r)
    (Q : (Fin r → Fin n) → ℝ) (R : Fin n → ℝ) :
    (∑ b : Fin r → Fin n,
      Q b * R (b j) *
        ∏ k ∈ Finset.univ.erase j,
          if a k = b k then (1 : ℝ) else 0) =
      ∑ l : Fin n, Q (Function.update a j l) * R l := by
  classical
  let e := Equiv.piSplitAt j (fun _ : Fin r ↦ Fin n)
  let a' : {k : Fin r // k ≠ j} → Fin n := fun k ↦ a k
  let f : (Fin r → Fin n) → ℝ := fun b ↦
    Q b * R (b j) * ∏ k ∈ Finset.univ.erase j, if a k = b k then (1 : ℝ) else 0
  have hmatch (l : Fin n) (c : {k : Fin r // k ≠ j} → Fin n) :
      (∀ k : Fin r, k ≠ j → a k = (e.symm (l, c)) k) ↔ a' = c := by
    constructor
    · intro h
      funext k
      simpa only [e, Equiv.piSplitAt_symm_apply, dif_neg k.2] using h k k.2
    · intro h k hk
      have hc := congrFun h ⟨k, hk⟩
      simpa only [e, Equiv.piSplitAt_symm_apply, dif_neg hk] using hc
  change (∑ b, f b) = _
  rw [← e.symm.sum_comp f, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro l _
  calc
    (∑ c, f (e.symm (l, c))) =
        ∑ c, if a' = c then Q (e.symm (l, c)) * R l else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      dsimp only [f]
      rw [kronecker_product_erase_eq]
      simp only [hmatch]
      have hj : e.symm (l, c) j = l := by simp [e, Equiv.piSplitAt]
      rw [hj]
      split_ifs <;> simp
    _ = Q (e.symm (l, a')) * R l := by simp
    _ = Q (Function.update a j l) * R l := by
      rw [show e.symm (l, a') = Function.update a j l from piSplitAt_symm_eq_update a j l]

set_option maxHeartbeats 800000 in

private theorem hasDerivAt_kronecker_contraction {r n : ℕ}
    (C : ℝ → (Fin r → Fin n) → ℝ)
    (H : ℝ → Fin n → Fin n → ℝ)
    (P : (Fin r → Fin n) → ℝ) (R : Fin n → Fin n → ℝ)
    {t : ℝ}
    (hC : ∀ a, HasDerivAt (fun s => C s a) (P a) t)
    (hH : ∀ i j, HasDerivAt (fun s => H s i j) (2 * R i j) t)
    (hHt : ∀ i j, H t i j = if i = j then (1 : ℝ) else 0) :
    HasDerivAt
      (fun s => ∑ a : Fin r → Fin n, ∑ b : Fin r → Fin n,
        C s a * C s b * ∏ j : Fin r, H s (a j) (b j))
      (2 * (∑ a : Fin r → Fin n, C t a * P a) +
        2 * (∑ j : Fin r, ∑ a : Fin r → Fin n, ∑ l : Fin n,
          R (a j) l * C t a * C t (Function.update a j l))) t := by
  classical
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun b _ =>
      ((hC a).mul (hC b)).mul
        (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun j _ => hH (a j) (b j)))))
  apply hd.congr_deriv
  simp only [hHt, smul_eq_mul, Pi.mul_apply]
  have hcoeff (a : Fin r → Fin n) :
      (∑ b : Fin r → Fin n,
        (P a * C t b + C t a * P b) *
          ∏ j : Fin r, if a j = b j then (1 : ℝ) else 0) =
        2 * (C t a * P a) := by
    rw [sum_mul_kronecker_product]
    ring
  have hslot (a : Fin r → Fin n) (j : Fin r) :
      (∑ b : Fin r → Fin n, C t a * C t b *
        ((∏ k ∈ Finset.univ.erase j, if a k = b k then (1 : ℝ) else 0) *
          (2 * R (a j) (b j)))) =
        2 * (∑ l : Fin n, R (a j) l * C t a * C t (Function.update a j l)) := by
    calc
      _ = (2 * C t a) * (∑ b : Fin r → Fin n,
          C t b * R (a j) (b j) *
            ∏ k ∈ Finset.univ.erase j, if a k = b k then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by
        rw [sum_mul_kronecker_product_erase]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
  calc
    _ = ∑ a : Fin r → Fin n,
        (2 * (C t a * P a) +
          2 * (∑ j : Fin r, ∑ l : Fin n,
            R (a j) l * C t a * C t (Function.update a j l))) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_add_distrib, hcoeff]
      congr 1
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Finset.mul_sum] using hslot a j
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]

private theorem tangent_finrank_eq (x : M) :
    Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n
  simp

private theorem exists_orthonormal_frame_equiv
    (g : RiemannianMetric n M) (x : M)
    (hd : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x,
      ∀ i : Fin n,
        e (EuclideanSpace.basisFun (Fin n) ℝ i) =
          g.orthonormalBasis x (Fin.cast hd.symm i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  let bn := b.reindex (finCongr hd)
  refine ⟨bn.repr.symm.toContinuousLinearEquiv, ?_⟩
  intro i
  change bn.repr.symm (EuclideanSpace.basisFun (Fin n) ℝ i) = _
  rw [EuclideanSpace.basisFun_apply, bn.repr_symm_single]
  exact b.reindex_apply (finCongr hd) i

private theorem sum_tuple_finCongr {r d n : ℕ} (h : d = n)
    (Q : (Fin r → Fin d) → ℝ) :
    (∑ a : Fin r → Fin n, Q (fun i => Fin.cast h.symm (a i))) =
      ∑ a : Fin r → Fin d, Q a := by
  cases h
  rfl

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_flow_tensorNorm_sq
    (F : RicciFlow n M J) {r : ℕ}
    (T : ℝ → CovariantTensorEvaluation n M r)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    {t : ℝ} (ht : t ∈ interior J) (x : M)
    (P : (Fin r → TangentSpace (𝓡 n) x) → ℝ)
    (hTime : ∀ v, HasDerivAt (fun s => T s x v) (P v) t) :
    let b := (F.metric t).orthonormalBasis x
    let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
    HasDerivAt (fun s => ((F.metric s).tensorNorm (T s) x) ^ 2)
      (2 * (∑ a : Fin r → Fin d,
        T t x (fun i => b (a i)) * P (fun i => b (a i))) +
        2 * (∑ j : Fin r, ∑ a : Fin r → Fin d, ∑ l : Fin d,
          (F.connection t).ricci x (b (a j)) (b l) *
            T t x (fun i => b (a i)) *
            T t x (fun i => b (Function.update a j l i)))) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let b := (F.metric t).orthonormalBasis x
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  have hd : d = n := tangent_finrank_eq x
  obtain ⟨e, he⟩ := exists_orthonormal_frame_equiv (F.metric t) x hd
  have hON (i j : Fin n) :
      (F.metric t).inner x (e (b0 i)) (e (b0 j)) =
        if i = j then (1 : ℝ) else 0 := by
    rw [he, he]
    change inner ℝ (b (Fin.cast hd.symm i)) (b (Fin.cast hd.symm j)) = _
    simp only [b.inner_eq_ite, Fin.cast_inj]
  let C : ℝ → (Fin r → Fin n) → ℝ := fun s a => T s x (fun i => e (b0 (a i)))
  let H : ℝ → Fin n → Fin n → ℝ :=
    fun s i j => frameInverseGram (F.metric s) x e.toContinuousLinearMap i j
  let R : Fin n → Fin n → ℝ := fun i j => (F.connection t).ricci x (e (b0 i)) (e (b0 j))
  have hC (a : Fin r → Fin n) : HasDerivAt (fun s => C s a)
      (P (fun i => e (b0 (a i)))) t := hTime _
  have hH (i j : Fin n) : HasDerivAt (fun s => H s i j) (2 * R i j) t :=
    hasDerivAt_flow_frameInverseGram F ht x e hON i j
  have hHt (i j : Fin n) : H t i j = if i = j then (1 : ℝ) else 0 := by
    change inner ℝ (b0 i)
      ((frameGramOperator (F.metric t) x e.toContinuousLinearMap).inverse (b0 j)) = _
    rw [frameGramOperator_eq_id_of_orthonormal (F.metric t) x e hON,
      ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]
    exact b0.inner_eq_ite i j
  have h := hasDerivAt_kronecker_contraction C H
    (fun a => P (fun i => e (b0 (a i)))) R hC hH hHt
  have hnorm : (fun s => ((F.metric s).tensorNorm (T s) x) ^ 2) =
      (fun s => ∑ a : Fin r → Fin n, ∑ a' : Fin r → Fin n,
        C s a * C s a' * ∏ j : Fin r, H s (a j) (a' j)) := by
    funext s
    exact tensorNorm_sq_eq_inverseGram (F.metric s) (T s) x ((hT s).1 x) e
  rw [hnorm]
  apply h.congr_deriv
  dsimp only [C, R, b0]
  simp only [he]
  have hupdate (a : Fin r → Fin n) (j : Fin r) (l : Fin n) :
      (fun i => b (Fin.cast hd.symm (Function.update a j l i))) =
        (fun i => b (Function.update (fun i => Fin.cast hd.symm (a i)) j
          (Fin.cast hd.symm l) i)) := by
    funext i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  dsimp only [b] at hupdate
  congr 1
  · exact congrArg (fun z : ℝ => 2 * z)
      (sum_tuple_finCongr hd (fun a : Fin r → Fin d =>
        T t x (fun i => b (a i)) * P (fun i => b (a i))))
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = ∑ a : Fin r → Fin n, ∑ l : Fin d,
          (F.connection t).ricci x (b (Fin.cast hd.symm (a j))) (b l) *
            T t x (fun i => b (Fin.cast hd.symm (a i))) *
            T t x (fun i => b (Function.update (fun i => Fin.cast hd.symm (a i)) j l i)) := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [hupdate]
        exact (finCongr hd.symm).sum_comp (fun l : Fin d =>
          (F.connection t).ricci x (b (Fin.cast hd.symm (a j))) (b l) *
            T t x (fun i => b (Fin.cast hd.symm (a i))) *
            T t x (fun i => b (Function.update (fun i => Fin.cast hd.symm (a i)) j l i)))
      _ = _ := sum_tuple_finCongr hd (fun a : Fin r → Fin d =>
        ∑ l : Fin d, (F.connection t).ricci x (b (a j)) (b l) *
          T t x (fun i => b (a i)) * T t x (fun i => b (Function.update a j l i)))


end PoincareConjecture.RicciFlowAnalysis

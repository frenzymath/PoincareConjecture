import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Tensor.FlowRiemannRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.QuadraticRicci
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

noncomputable def frameGramOperator (g : RiemannianMetric n M) (x : M)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) x) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  Q.toContinuousLinearMap.comp ((g.inner x).bilinearComp L L)

noncomputable def frameInverseGram (g : RiemannianMetric n M) (x : M)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) x)
    (i j : Fin n) : ℝ :=
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  inner ℝ (b0 i) ((frameGramOperator g x L).inverse (b0 j))

private theorem frameGramOperator_inner (g : RiemannianMetric n M) (x : M)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] TangentSpace (𝓡 n) x)
    (v w : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (frameGramOperator g x L v) w = g.inner x (L v) (L w) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
      (((g.inner x).bilinearComp L L) v)) w = _
  exact InnerProductSpace.toDual_symm_apply

theorem frameGramOperator_isInvertible (g : RiemannianMetric n M) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x) :
    (frameGramOperator g x e.toContinuousLinearMap).IsInvertible := by
  let A := frameGramOperator g x e.toContinuousLinearMap
  have hker (v : EuclideanSpace ℝ (Fin n)) (hv : A v = 0) : v = 0 := by
    have hpair : g.inner x (e v) (e v) = 0 := by
      have h := frameGramOperator_inner g x e.toContinuousLinearMap v v
      change inner ℝ (A v) v = g.inner x (e v) (e v) at h
      rw [hv, inner_zero_left] at h
      exact h.symm
    have hev : e v = 0 := by
      by_contra hne
      exact (ne_of_gt (g.pos x (e v) hne)) hpair
    apply e.injective
    simpa only [map_zero] using hev
  have hinj : Function.Injective A := by
    intro v w h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, h, sub_self]
  have hsurj : Function.Surjective A := LinearMap.injective_iff_surjective.mp hinj
  exact ⟨(LinearEquiv.ofBijective A.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    by ext v; rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem frameInverseGram_eq_coordinate_sum
    (g : RiemannianMetric n M) (x : M)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x)
    (i j : Fin n) :
    let b0 := EuclideanSpace.basisFun (Fin n) ℝ
    let b := g.orthonormalBasis x
    (∑ a, inner ℝ (b0 i) (e.symm (b a)) *
      inner ℝ (b0 j) (e.symm (b a))) =
      frameInverseGram g x e.toContinuousLinearMap i j := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let b := g.orthonormalBasis x
  let A := frameGramOperator g x e.toContinuousLinearMap
  let z (k : Fin n) := e (A.inverse (b0 k))
  have hInv : A.IsInvertible := frameGramOperator_isInvertible g x e
  have hpair (k : Fin n) (v : TangentSpace (𝓡 n) x) :
      g.inner x (z k) v = inner ℝ (b0 k) (e.symm v) := by
    have h := frameGramOperator_inner g x e.toContinuousLinearMap
      (A.inverse (b0 k)) (e.symm v)
    change inner ℝ (A (A.inverse (b0 k))) (e.symm v) =
      g.inner x (z k) (e (e.symm v)) at h
    rw [hInv.self_apply_inverse, e.apply_symm_apply] at h
    exact h.symm
  change (∑ a, inner ℝ (b0 i) (e.symm (b a)) *
    inner ℝ (b0 j) (e.symm (b a))) = _
  calc
    _ = ∑ a, inner ℝ (z i) (b a) * inner ℝ (b a) (z j) := by
      apply Finset.sum_congr rfl
      intro a _
      change _ = g.inner x (z i) (b a) * g.inner x (b a) (z j)
      rw [g.symm x (b a) (z j), hpair i (b a), hpair j (b a)]
    _ = inner ℝ (z i) (z j) := b.sum_inner_mul_inner (z i) (z j)
    _ = inner ℝ (b0 i) (e.symm (z j)) := hpair i (z j)
    _ = inner ℝ (b0 i) (A.inverse (b0 j)) := by
      change inner ℝ (b0 i) (e.symm (e (A.inverse (b0 j)))) = _
      rw [e.symm_apply_apply]
    _ = frameInverseGram g x e.toContinuousLinearMap i j := rfl

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem tensorNorm_sq_eq_inverseGram
    (g : RiemannianMetric n M) {r : ℕ}
    (T : CovariantTensorEvaluation n M r) (x : M)
    (hT : ∃ A : MultilinearMap ℝ
      (fun _ : Fin r => TangentSpace (𝓡 n) x) ℝ,
      ∀ v, T x v = A v)
    (e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) x) :
    let b0 := EuclideanSpace.basisFun (Fin n) ℝ
    (g.tensorNorm T x) ^ 2 =
      ∑ a : Fin r → Fin n, ∑ b : Fin r → Fin n,
        T x (fun j => e (b0 (a j))) * T x (fun j => e (b0 (b j))) *
        ∏ j : Fin r,
          frameInverseGram g x e.toContinuousLinearMap (a j) (b j) := by
  classical
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let b := g.orthonormalBasis x
  let d := Module.finrank ℝ (TangentSpace (𝓡 n) x)
  let c (i : Fin n) (v : TangentSpace (𝓡 n) x) := inner ℝ (b0 i) (e.symm v)
  let val (a : Fin r → Fin n) := T x (fun j => e (b0 (a j)))
  obtain ⟨A, hA⟩ := hT
  have hrec (v : TangentSpace (𝓡 n) x) :
      (∑ i, c i v • e (b0 i)) = v := by
    calc
      _ = e (∑ i, c i v • b0 i) := by simp only [map_sum, map_smul]
      _ = e (e.symm v) := congrArg e (b0.sum_repr' (e.symm v))
      _ = v := e.apply_symm_apply v
  have hExpand (v : Fin r → TangentSpace (𝓡 n) x) :
      T x v = ∑ a : Fin r → Fin n, (∏ j, c (a j) (v j)) * val a := by
    rw [hA v]
    calc
      A v = A (fun j => ∑ i, c i (v j) • e (b0 i)) := by simp only [hrec]
      _ = ∑ a : Fin r → Fin n, A (fun j => c (a j) (v j) • e (b0 (a j))) :=
        A.map_sum _
      _ = _ := by simp only [A.map_smul_univ, smul_eq_mul, val, hA]
  have hSquare (a : Fin r → Fin d) :
      (T x (fun j => b (a j))) ^ 2 =
        ∑ v : Fin r → Fin n, ∑ w : Fin r → Fin n,
          val v * val w * ∏ j, (c (v j) (b (a j)) * c (w j) (b (a j))) := by
    rw [hExpand (fun j => b (a j)), pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.prod_mul_distrib]
    ring
  change (g.tensorNorm T x) ^ 2 =
    ∑ a : Fin r → Fin n, ∑ b : Fin r → Fin n,
      val a * val b * ∏ j, frameInverseGram g x e.toContinuousLinearMap (a j) (b j)
  calc
    _ = ∑ a : Fin r → Fin d, (T x (fun j => b (a j))) ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = ∑ a : Fin r → Fin d, ∑ v : Fin r → Fin n, ∑ w : Fin r → Fin n,
        val v * val w * ∏ j, (c (v j) (b (a j)) * c (w j) (b (a j))) := by
      exact Finset.sum_congr rfl (fun a _ => hSquare a)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.mul_sum]
      rw [← Fintype.prod_sum (fun j k => c (v j) (b k) * c (w j) (b k))]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact frameInverseGram_eq_coordinate_sum g x e (v j) (w j)

end PoincareConjecture.RicciFlowAnalysis

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem frameGramOperator_eq_sum (g : RiemannianMetric n M) (x : M)
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
  have hcoef (i : Fin n) :
      inner ℝ (b0 i) (frameGramOperator g x L v) =
        ∑ j, g.inner x (L (b0 i)) (L (b0 j)) * inner ℝ (b0 j) v := by
    calc
      _ = g.inner x (L (b0 i)) (L v) := by
        rw [real_inner_comm, frameGramOperator_inner, g.symm]
      _ = g.inner x (L (b0 i)) (L (∑ j, inner ℝ (b0 j) v • b0 j)) := by
        rw [b0.sum_repr']
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  calc
    _ = ∑ i, inner ℝ (b0 i) (frameGramOperator g x L v) • b0 i :=
      (b0.sum_repr' _).symm
    _ = ∑ i, (∑ j, g.inner x (L (b0 i)) (L (b0 j)) * inner ℝ (b0 j) v) • b0 i := by
      simp only [hcoef]
    _ = _ := by
      simp only [sum_apply, smul_apply, InnerProductSpace.rankOne_apply,
        Finset.sum_smul, smul_smul, b0]

private theorem contMDiffOn_frameVector (c : M) (i : Fin n) :
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (fun y => e.symmL ℝ y (EuclideanSpace.basisFun (Fin n) ℝ i)))
      e.baseSet := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  apply (e.contMDiffOn_localFrame_baseSet ∞ b0.toBasis i).congr
  intro y hy
  apply congrArg (Bundle.TotalSpace.mk y)
  change e.symmL ℝ y (b0 i) = e.localFrame b0.toBasis i y
  simp only [e.localFrame_apply_of_mem_baseSet b0.toBasis hy,
    Bundle.Trivialization.basisAt, Module.Basis.map_apply,
    Bundle.Trivialization.linearEquivAt_symm_apply, e.symmL_apply hy]
  rfl

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_frameInverseGram
    (F : RicciFlow n M J) (c : M) (i j : Fin n) :
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        frameInverseGram (F.metric p.1) p.2 (e.symmL ℝ p.2) i j)
      (J ×ˢ e.baseSet) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  let V := J ×ˢ e.baseSet
  let X (a : Fin n) := fun y => e.symmL ℝ y (b0 a)
  let A : ℝ × M → E →L[ℝ] E :=
    fun p => frameGramOperator (F.metric p.1) p.2 (e.symmL ℝ p.2)
  change ContMDiffOn I 𝓘(ℝ, ℝ) ∞
    (fun p : ℝ × M => inner ℝ (b0 i) ((A p).inverse (b0 j))) V
  have hX (a : Fin n) : ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (X a)) e.baseSet := contMDiffOn_frameVector c a
  have hXtime (a : Fin n) :
      ContMDiffOn I ((𝓡 n).prod 𝓘(ℝ, E)) ∞
        (fun p : ℝ × M => Bundle.TotalSpace.mk' E p.2 (X a p.2)) V :=
    (hX a).comp contMDiffOn_snd (fun _ hp => hp.2)
  have hG (a b : Fin n) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.metric p.1).inner p.2 (X a p.2) (X b p.2)) V := by
    intro p hp
    have hm := (F.smooth p ⟨hp.1, mem_univ p.2⟩).mono
      (show V ⊆ J ×ˢ univ from fun q hq => ⟨hq.1, mem_univ q.2⟩)
    have he : ContMDiffWithinAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
        (fun q => Bundle.TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) q.2
          ((F.metric q.1).inner q.2 (X a q.2) (X b q.2))) V p :=
      hm.clm_bundle_apply₂ (hXtime a p hp) (hXtime b p hp)
    simp only [Bundle.contMDiffWithinAt_totalSpace] at he
    exact he.2
  have hA : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞ A V := by
    have hs : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) ∞
        (fun p : ℝ × M => ∑ a : Fin n, ∑ b : Fin n,
          (F.metric p.1).inner p.2 (X a p.2) (X b p.2) •
            InnerProductSpace.rankOne ℝ (b0 a) (b0 b)) V := by
      intro p hp
      apply ContMDiffWithinAt.sum
      intro a _
      apply ContMDiffWithinAt.sum
      intro b _
      exact (hG a b p hp).smul contMDiffWithinAt_const
    apply hs.congr
    intro p hp
    exact frameGramOperator_eq_sum (F.metric p.1) p.2 (e.symmL ℝ p.2)
  intro p hp
  let ep := (e.continuousLinearEquivAt ℝ p.2 hp.2).symm
  have hep : ep.toContinuousLinearMap = e.symmL ℝ p.2 :=
    e.symm_continuousLinearEquivAt_eq' hp.2
  have hInv : (A p).IsInvertible := by
    have h := frameGramOperator_isInvertible (F.metric p.1) p.2 ep
    rwa [hep] at h
  have hAi : ContMDiffWithinAt I 𝓘(ℝ, E →L[ℝ] E) ∞
      (fun q => (A q).inverse) V p :=
    hInv.contDiffAt_map_inverse.contMDiffAt.comp_contMDiffWithinAt p (hA p hp)
  have hvec : ContMDiffWithinAt I 𝓘(ℝ, E) ∞
      (fun q => (A q).inverse (b0 j)) V p :=
    hAi.clm_apply contMDiffWithinAt_const
  exact (innerSL ℝ (b0 i)).contMDiffAt.comp_contMDiffWithinAt p hvec

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_tensorNorm_sq
    (F : RicciFlow n M J) {r : ℕ}
    (T : ℝ → CovariantTensorEvaluation n M r)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hTime : ∀ U : Set M, IsOpen U →
      ∀ X : Fin r → (y : M) → TangentSpace (𝓡 n) y,
        (∀ i, ContMDiffOn (𝓡 n)
          ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (X i)) U) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => T p.1 p.2 (fun i => X i p.2)) (J ×ˢ U)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ((F.metric p.1).tensorNorm (T p.1) p.2) ^ 2)
      (J ×ˢ Set.univ) := by
  classical
  intro p0 hp0
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p0.2
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let I := 𝓘(ℝ, ℝ).prod (𝓡 n)
  let V := J ×ˢ e.baseSet
  let C (a : Fin r → Fin n) := fun p : ℝ × M =>
    T p.1 p.2 (fun j => e.symmL ℝ p.2 (b0 (a j)))
  let H := fun p : ℝ × M => ∑ a : Fin r → Fin n, ∑ b : Fin r → Fin n,
    C a p * C b p * ∏ j : Fin r,
      frameInverseGram (F.metric p.1) p.2 (e.symmL ℝ p.2) (a j) (b j)
  have hc : p0.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p0.2
  have hC (a : Fin r → Fin n) : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (C a) V :=
    hTime e.baseSet e.open_baseSet
      (fun j y => e.symmL ℝ y (b0 (a j)))
      (fun j => contMDiffOn_frameVector p0.2 (a j))
  have hH : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ H V := by
    intro p hp
    apply ContMDiffWithinAt.sum
    intro a _
    apply ContMDiffWithinAt.sum
    intro b _
    apply ContMDiffWithinAt.mul
    · exact (hC a p hp).mul (hC b p hp)
    · apply ContMDiffWithinAt.prod
      intro j _
      exact contMDiffOn_flow_frameInverseGram F p0.2 (a j) (b j) p hp
  have hnorm : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => ((F.metric p.1).tensorNorm (T p.1) p.2) ^ 2) V := by
    apply hH.congr
    intro p hp
    let ep := (e.continuousLinearEquivAt ℝ p.2 hp.2).symm
    have hep : ep.toContinuousLinearMap = e.symmL ℝ p.2 :=
      e.symm_continuousLinearEquivAt_eq' hp.2
    have hev (v : E) : ep v = e.symmL ℝ p.2 v :=
      congrArg (fun L : E →L[ℝ] TangentSpace (𝓡 n) p.2 => L v) hep
    have h := tensorNorm_sq_eq_inverseGram (F.metric p.1) (T p.1) p.2
      ((hT p.1).1 p.2) ep
    change ((F.metric p.1).tensorNorm (T p.1) p.2) ^ 2 =
      ∑ a : Fin r → Fin n, ∑ b : Fin r → Fin n,
        T p.1 p.2 (fun j => ep (b0 (a j))) * T p.1 p.2 (fun j => ep (b0 (b j))) *
          ∏ j, frameInverseGram (F.metric p.1) p.2 ep.toContinuousLinearMap (a j) (b j) at h
    rw [hep] at h
    have hCeq (a : Fin r → Fin n) :
        T p.1 p.2 (fun j => ep (b0 (a j))) = C a p := by
      apply congrArg (T p.1 p.2)
      funext j
      exact hev (b0 (a j))
    simpa only [hCeq] using h
  apply (hnorm p0 ⟨hp0.1, hc⟩).mono_of_mem_nhdsWithin
  exact nhdsWithin_prod self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (e.open_baseSet.mem_nhds hc))

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_flow_curvatureDerivativeEnergy
    (F : RicciFlow n M J) (m : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        ((F.connection p.1).curvatureDerivativeNorm m p.2) ^ 2)
      (J ×ˢ Set.univ) := by
  have hsmooth (s : ℝ) (k : ℕ) :
      IsSmoothCovariantTensor
        ((F.connection s).iteratedCovariantTensorDerivative
          (F.connection s).riemannEvaluation k) := by
    induction k with
    | zero => exact isSmoothCovariantTensor_riemannEvaluation (F.connection s)
    | succ k ih => exact isSmoothCovariantTensor_covariantTensorDerivative (F.connection s) ih
  exact contMDiffOn_flow_tensorNorm_sq F
    (fun s => (F.connection s).iteratedCovariantTensorDerivative
      (F.connection s).riemannEvaluation m)
    (fun s => hsmooth s m)
    (fun U hU X hX => contMDiffOn_flow_iteratedCovariantTensorDerivative F
      (fun s => isSmoothCovariantTensor_riemannEvaluation (F.connection s))
      (fun V hV Y hY => contMDiffOn_flow_riemannEvaluation F hV Y hY)
      m hU hX)

end PoincareConjecture.RicciFlowAnalysis

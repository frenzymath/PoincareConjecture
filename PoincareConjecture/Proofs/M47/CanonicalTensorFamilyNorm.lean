import PoincareConjecture.Proofs.M47.CanonicalTensorFamilyDerivatives
import PoincareConjecture.Proofs.M04.FlowCurvatureEnergy









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.Proofs.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

private theorem contMDiffOn_fixedFrameVector (c : M) (v : EuclideanSpace ℝ (Fin n)) :
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
      (T% (fun y ↦ e.symmL ℝ y v)) e.baseSet := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
  have hc : c ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' c
  apply (M04.contMDiffOn_extend_baseSet (e.symmL ℝ c v)).congr
  intro y hy
  apply congrArg (Bundle.TotalSpace.mk y)
  change e.symmL ℝ y v = e.symm y (e ⟨c, e.symmL ℝ c v⟩).2
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) e hc,
    e.continuousLinearMapAt_symmL hc, e.symmL_apply hy]



theorem continuousOn_fixed_frameInverseGram (g : RiemannianMetric n M)
    (c : M) (i j : Fin n) :
    let E := EuclideanSpace ℝ (Fin n)
    let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
    ContinuousOn (fun y ↦ M04.frameInverseGram g y (e.symmL ℝ y) i j) e.baseSet := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let B : M → E →L[ℝ] E →L[ℝ] ℝ := fun y ↦
    (g.inner y).bilinearComp (e.symmL ℝ y) (e.symmL ℝ y)
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let A : M → E →L[ℝ] E := fun y ↦ M04.frameGramOperator g y (e.symmL ℝ y)
  have hB : ContinuousOn B e.baseSet := by
    apply continuousOn_clm_apply.mpr
    intro v
    apply continuousOn_clm_apply.mpr
    intro w
    exact ((contMDiffOn_fixedFrameVector c v).inner_bundle
      (contMDiffOn_fixedFrameVector c w)).continuousOn
  have hA : ContinuousOn A e.baseSet := continuousOn_const.clm_comp hB
  change ContinuousOn (fun y ↦ inner ℝ (b0 i) ((A y).inverse (b0 j))) e.baseSet
  intro y hy
  let ep := (e.continuousLinearEquivAt ℝ y hy).symm
  have hep : ep.toContinuousLinearMap = e.symmL ℝ y :=
    e.symm_continuousLinearEquivAt_eq' hy
  have hInv : (A y).IsInvertible := by
    have h := M04.frameGramOperator_isInvertible g y ep
    rwa [hep] at h
  have hAi : ContinuousWithinAt (fun z ↦ (A z).inverse) e.baseSet y :=
    (hInv.contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt (hA y hy)
  exact continuousWithinAt_const.inner (hAi.clm_apply continuousWithinAt_const)



theorem continuousOn_fixed_tensorNorm_sq (g : RiemannianMetric n M) {r : ℕ}
    (T : ℝ → CovariantTensorEvaluation n M r)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hTime : ∀ U : Set M, IsOpen U →
      ∀ X : Fin r → (y : M) → TangentSpace (𝓡 n) y,
        (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (X i)) U) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ T p.1 p.2 (fun i ↦ X i p.2)) (J ×ˢ U)) :
    ContinuousOn (fun p : ℝ × M ↦ (g.tensorNorm (T p.1) p.2) ^ 2) (J ×ˢ univ) := by
  classical
  intro p0 hp0
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) p0.2
  let b0 := EuclideanSpace.basisFun (Fin n) ℝ
  let V := J ×ˢ e.baseSet
  let C (a : Fin r → Fin n) := fun p : ℝ × M ↦
    T p.1 p.2 (fun j ↦ e.symmL ℝ p.2 (b0 (a j)))
  let H := fun p : ℝ × M ↦ ∑ a : Fin r → Fin n, ∑ b : Fin r → Fin n,
    C a p * C b p * ∏ j : Fin r, M04.frameInverseGram g p.2 (e.symmL ℝ p.2) (a j) (b j)
  have hc : p0.2 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p0.2
  have hC (a : Fin r → Fin n) : ContinuousOn (C a) V :=
    (hTime e.baseSet e.open_baseSet (fun j y ↦ e.symmL ℝ y (b0 (a j)))
      (fun j ↦ contMDiffOn_fixedFrameVector p0.2 (b0 (a j)))).continuousOn
  have hG (i j : Fin n) : ContinuousOn
      (fun p : ℝ × M ↦ M04.frameInverseGram g p.2 (e.symmL ℝ p.2) i j) V :=
    (continuousOn_fixed_frameInverseGram g p0.2 i j).comp continuousOn_snd (fun _ hp ↦ hp.2)
  have hH : ContinuousOn H V := by
    apply continuousOn_finsetSum
    intro a _
    apply continuousOn_finsetSum
    intro b _
    apply (hC a |>.mul (hC b)).mul
    apply continuousOn_finsetProd
    intro j _
    exact hG (a j) (b j)
  have hnorm : ContinuousOn (fun p : ℝ × M ↦ (g.tensorNorm (T p.1) p.2) ^ 2) V := by
    apply hH.congr
    intro p hp
    let ep := (e.continuousLinearEquivAt ℝ p.2 hp.2).symm
    have hep : ep.toContinuousLinearMap = e.symmL ℝ p.2 :=
      e.symm_continuousLinearEquivAt_eq' hp.2
    have hev (v : E) : ep v = e.symmL ℝ p.2 v :=
      congrArg (fun L : E →L[ℝ] TangentSpace (𝓡 n) p.2 ↦ L v) hep
    have h := M04.tensorNorm_sq_eq_inverseGram g (T p.1) p.2 ((hT p.1).1 p.2) ep
    change (g.tensorNorm (T p.1) p.2) ^ 2 =
      ∑ a : Fin r → Fin n, ∑ b : Fin r → Fin n,
        T p.1 p.2 (fun j ↦ ep (b0 (a j))) * T p.1 p.2 (fun j ↦ ep (b0 (b j))) *
          ∏ j, M04.frameInverseGram g p.2 ep.toContinuousLinearMap (a j) (b j) at h
    rw [hep] at h
    have hCeq (a : Fin r → Fin n) : T p.1 p.2 (fun j ↦ ep (b0 (a j))) = C a p := by
      apply congrArg (T p.1 p.2)
      funext j
      exact hev (b0 (a j))
    simpa only [hCeq] using h
  apply (hnorm p0 ⟨hp0.1, hc⟩).mono_of_mem_nhdsWithin
  exact nhdsWithin_prod self_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds (e.open_baseSet.mem_nhds hc))



theorem continuousOn_fixed_tensorJetEnergy (g : RiemannianMetric n M)
    (D : LeviCivitaData g) {r : ℕ} (T : ℝ → CovariantTensorEvaluation n M r)
    (hT : ∀ s, IsSmoothCovariantTensor (T s))
    (hTime : ∀ U : Set M, IsOpen U →
      ∀ X : Fin r → (y : M) → TangentSpace (𝓡 n) y,
        (∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          ∞ (T% (X i)) U) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M ↦ T p.1 p.2 (fun i ↦ X i p.2)) (J ×ˢ U))
    (k : ℕ) :
    ContinuousOn (fun p : ℝ × M ↦ ∑ j ∈ Finset.range (k + 1),
      (g.tensorNorm (D.iteratedCovariantTensorDerivative (T p.1) j) p.2) ^ 2)
      (J ×ˢ univ) := by
  apply continuousOn_finsetSum
  intro j _
  have hsmooth (s : ℝ) (m : ℕ) :
      IsSmoothCovariantTensor (D.iteratedCovariantTensorDerivative (T s) m) := by
    induction m with
    | zero => exact hT s
    | succ m ih => exact M04.isSmoothCovariantTensor_covariantTensorDerivative D ih
  exact continuousOn_fixed_tensorNorm_sq g (fun s ↦ D.iteratedCovariantTensorDerivative (T s) j)
    (fun s ↦ hsmooth s j)
    (fun U hU X hX ↦ contMDiffOn_fixed_iteratedCovariantTensorDerivative D hT hTime j hU hX)

end PoincareConjecture.Proofs.M47

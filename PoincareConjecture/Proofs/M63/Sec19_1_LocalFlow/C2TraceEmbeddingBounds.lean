import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.EmbeddingHessianVector
import PoincareConjecture.Proofs.M62.Cor0_3_AmbientBounds
import PoincareConjecture.Proofs.M62.Cor0_3_PointwiseBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle Manifold
open scoped Manifold ContDiff Bundle BigOperators

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem exists_uniform_embedding_derivative_bounds
    (F : RicciFlow n M (Icc a b)) (hcompact : IsCompact (univ : Set M))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e) :
    ∃ E1 E2 E3 : ℝ, (0 ≤ E1 ∧ 0 ≤ E2 ∧ 0 ≤ E3) ∧
      ∀ t ∈ Icc a b, ∀ p : M, ∀ V Y Z : TangentSpace (𝓡 n) p,
        Norm.norm (E := W) (mfderiv (𝓡 n) 𝓘(ℝ, W) e p V) ≤
            E1 * (F.metric t).tangentNorm p V ∧
          ‖coordinateHessian (F.connection t) e p V Y‖ ≤
            E2 * (F.metric t).tangentNorm p V * (F.metric t).tangentNorm p Y ∧
          ‖WithLp.toLp 2 (fun i : ι => (F.connection t).covariantTensorDerivative
              (fun q w => (F.connection t).hessian (fun z => e z i) q (w 0) (w 1))
              p ![V, Y, Z])‖ ≤
            E3 * (F.metric t).tangentNorm p V * (F.metric t).tangentNorm p Y *
              (F.metric t).tangentNorm p Z := by
  classical
  let TimeRegular : {k : ℕ} → (ℝ → CovariantTensorEvaluation n M k) → Prop :=
    fun {k} T => ∀ U : Set M, IsOpen U →
      ∀ X : Fin k → (p : M) → TangentSpace (𝓡 n) p,
        (∀ j, ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% (X j)) U) →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => T p.1 p.2 (fun j => X j p.2)) (Icc a b ×ˢ U)
  have hstep {k : ℕ} (T : ℝ → CovariantTensorEvaluation n M k)
      (hT : ∀ t, IsSmoothCovariantTensor (T t)) (hTime : TimeRegular T) :
      TimeRegular (fun t => (F.connection t).covariantTensorDerivative (T t)) := by
    intro U hU X hX
    exact M04.contMDiffOn_flow_covariantTensorDerivative F hT hTime hU hX
  have hconstants (i : ι) : ∃ K1 K2 K3 : ℝ, (0 ≤ K1 ∧ 0 ≤ K2 ∧ 0 ≤ K3) ∧
      ∀ t ∈ Icc a b, ∀ p : M, ∀ V Y Z : TangentSpace (𝓡 n) p,
        |EuclideanSpace.proj i (mfderiv (𝓡 n) 𝓘(ℝ, W) e p V)| ≤
            K1 * (F.metric t).tangentNorm p V ∧
          |(F.connection t).hessian (fun z => e z i) p V Y| ≤
            K2 * (F.metric t).tangentNorm p V * (F.metric t).tangentNorm p Y ∧
          |(F.connection t).covariantTensorDerivative
              (fun q w => (F.connection t).hessian (fun z => e z i) q (w 0) (w 1))
              p ![V, Y, Z]| ≤
            K3 * (F.metric t).tangentNorm p V * (F.metric t).tangentNorm p Y *
              (F.metric t).tangentNorm p Z := by
    let f : M → ℝ := fun p => e p i
    have hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f :=
      (EuclideanSpace.proj i).contDiff.contMDiff.comp he
    let T0 : ℝ → CovariantTensorEvaluation n M 0 := fun _ p _ => f p
    let T1 : ℝ → CovariantTensorEvaluation n M 1 :=
      fun t => (F.connection t).covariantTensorDerivative (T0 t)
    let T2 : ℝ → CovariantTensorEvaluation n M 2 :=
      fun t => (F.connection t).covariantTensorDerivative (T1 t)
    let T3 : ℝ → CovariantTensorEvaluation n M 3 :=
      fun t => (F.connection t).covariantTensorDerivative (T2 t)
    have hs0 (t : ℝ) : IsSmoothCovariantTensor (T0 t) := by
      constructor
      · intro p
        exact ⟨MultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace (𝓡 n) p) (f p), fun _ => rfl⟩
      · intro U _hU _X _hX
        exact hf.contMDiffOn
    have ht0 : TimeRegular T0 := by
      intro U _hU _X _hX
      exact (hf.comp contMDiff_snd).contMDiffOn
    have hs1 (t : ℝ) : IsSmoothCovariantTensor (T1 t) :=
      M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t) (hs0 t)
    have ht1 : TimeRegular T1 := hstep T0 hs0 ht0
    have hs2 (t : ℝ) : IsSmoothCovariantTensor (T2 t) :=
      M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t) (hs1 t)
    have ht2 : TimeRegular T2 := hstep T1 hs1 ht1
    have hs3 (t : ℝ) : IsSmoothCovariantTensor (T3 t) :=
      M04.isSmoothCovariantTensor_covariantTensorDerivative (F.connection t) (hs2 t)
    have ht3 : TimeRegular T3 := hstep T2 hs2 ht2
    have hdf (t : ℝ) (p : M) (w : Fin 1 → TangentSpace (𝓡 n) p) :
        T1 t p w = mvfderiv (𝓡 n) f p (w 0) := by
      simp [T1, T0, LeviCivitaData.covariantTensorDerivative]
    have hhess (t : ℝ) (p : M) (w : Fin 2 → TangentSpace (𝓡 n) p) :
        T2 t p w = (F.connection t).hessian f p (w 0) (w 1) := by
      have h01 : (Fin.succ 0 : Fin 2) = 1 := by decide
      change (F.connection t).covariantTensorDerivative (T1 t) p w = _
      rw [LeviCivitaData.covariantTensorDerivative]
      simp only [hdf, Fin.sum_univ_succ, Fin.sum_univ_zero, Function.update_self,
        LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
        FiberBundle.extend_apply_self, add_zero, h01]
    have hT2 (t : ℝ) : T2 t =
        (fun p w => (F.connection t).hessian f p (w 0) (w 1)) := by
      funext p w
      exact hhess t p w
    have hproj (p : M) (V : TangentSpace (𝓡 n) p) :
        mvfderiv (𝓡 n) f p V = EuclideanSpace.proj i (mfderiv (𝓡 n) 𝓘(ℝ, W) e p V) := by
      let L : W →L[ℝ] ℝ := EuclideanSpace.proj i
      change mvfderiv (𝓡 n) (L ∘ e) p V = _
      rw [mvfderiv_comp_apply p L.differentiableAt.mdifferentiableAt
        (he.mdifferentiable (by simp) p) V]
      simpa only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace,
        ContinuousLinearMap.comp_apply] using!
        congrArg (fun K : W →L[ℝ] ℝ => K (mfderiv (𝓡 n) 𝓘(ℝ, W) e p V))
          (L.fderiv (x := e p))
    obtain ⟨K1, hK1, h1⟩ := M62.exists_uniform_tensor_bound F hcompact T1 hs1 ht1
    obtain ⟨K2, hK2, h2⟩ := M62.exists_uniform_tensor_bound F hcompact T2 hs2 ht2
    obtain ⟨K3, hK3, h3⟩ := M62.exists_uniform_tensor_bound F hcompact T3 hs3 ht3
    refine ⟨K1, K2, K3, ⟨hK1, hK2, hK3⟩, ?_⟩
    intro t ht p V Y Z
    refine ⟨?_, ?_, ?_⟩
    · simpa [hdf, hproj, Fin.prod_univ_succ] using
        M62.tensor_abs_le_of_unit_bound (F.metric t) (T1 t) (hs1 t) p (h1 t ht p) ![V]
    · simpa [hhess, f, Fin.prod_univ_succ, mul_assoc] using
        M62.tensor_abs_le_of_unit_bound (F.metric t) (T2 t) (hs2 t) p (h2 t ht p) ![V, Y]
    · simpa [T3, hT2, f, Fin.prod_univ_succ, mul_assoc] using
        M62.tensor_abs_le_of_unit_bound (F.metric t) (T3 t) (hs3 t) p (h3 t ht p) ![V, Y, Z]
  choose K1 K2 K3 hK hcoeff using hconstants
  let L : (ι → ℝ) →L[ℝ] W :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap
  have hnorm {f : ι → ℝ} {K : ι → ℝ} (hK : ∀ i, 0 ≤ K i) {r : ℝ} (hr : 0 ≤ r)
      (hbound : ∀ i, |f i| ≤ K i * r) : ‖L f‖ ≤ (‖L‖ * ∑ i, K i) * r := by
    have hsum : 0 ≤ ∑ i, K i := Finset.sum_nonneg (fun i _ => hK i)
    have hfnorm : ‖f‖ ≤ (∑ i, K i) * r := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hsum hr)).mpr
      intro i
      rw [Real.norm_eq_abs]
      exact (hbound i).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)) hr)
    calc
      ‖L f‖ ≤ ‖L‖ * ‖f‖ := L.le_opNorm f
      _ ≤ ‖L‖ * ((∑ i, K i) * r) := mul_le_mul_of_nonneg_left hfnorm (norm_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm
  refine ⟨‖L‖ * ∑ i, K1 i, ‖L‖ * ∑ i, K2 i, ‖L‖ * ∑ i, K3 i, ?_, ?_⟩
  · exact ⟨mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => (hK i).1),
      mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => (hK i).2.1),
      mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => (hK i).2.2)⟩
  · intro t ht p V Y Z
    have hV : 0 ≤ (F.metric t).tangentNorm p V := Real.sqrt_nonneg _
    have hY : 0 ≤ (F.metric t).tangentNorm p Y := Real.sqrt_nonneg _
    have hZ : 0 ≤ (F.metric t).tangentNorm p Z := Real.sqrt_nonneg _
    refine ⟨?_, ?_, ?_⟩
    · exact hnorm (fun i => (hK i).1) hV (fun i => (hcoeff i t ht p V Y Z).1)
    · have h := hnorm (fun i => (hK i).2.1) (mul_nonneg hV hY)
        (fun i => by simpa only [mul_assoc] using (hcoeff i t ht p V Y Z).2.1)
      simpa only [coordinateHessian, L, mul_assoc] using! h
    · have h := hnorm (fun i => (hK i).2.2) (mul_nonneg (mul_nonneg hV hY) hZ)
        (fun i => by simpa only [mul_assoc] using (hcoeff i t ht p V Y Z).2.2)
      simpa only [L, mul_assoc] using! h

end PoincareConjecture.M63

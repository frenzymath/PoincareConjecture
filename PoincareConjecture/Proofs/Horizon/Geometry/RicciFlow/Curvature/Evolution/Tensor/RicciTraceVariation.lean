import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.RiemannRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

set_option maxHeartbeats 2000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_ricci_of_curvature_derivative (F : RicciFlow n M J)
    {t : ℝ} (x : M) (u v : TangentSpace (𝓡 n) x)
    (r : TangentSpace (𝓡 n) x → TangentSpace (𝓡 n) x → ℝ)
    (ht : t ∈ interior J)
    (hRtime : ∀ a b,
      HasDerivAt (fun s ↦ (F.connection s).curvatureTensor x u a v b) (r a b) t) :
    HasDerivAt (fun s ↦ (F.connection s).ricci x u v)
      ((∑ i, r ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x i)) +
        2 * (∑ i, ∑ j, (F.connection t).ricci x
          ((F.metric t).orthonormalBasis x i) ((F.metric t).orthonormalBasis x j) *
          (F.connection t).curvatureTensor x u ((F.metric t).orthonormalBasis x i)
            v ((F.metric t).orthonormalBasis x j))) t := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let E := TangentSpace (𝓡 n) x
  let : FiniteDimensional ℝ E := VectorBundle.finiteDimensional ℝ
    (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n) : M → Type _) x
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  have hclm {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
      {L : ℝ → V →L[ℝ] W}
      (hL : ∀ a, DifferentiableAt ℝ (fun s ↦ L s a) t) :
      DifferentiableAt ℝ L t := by
    let d := Module.finrank ℝ V
    have hd : d = Module.finrank ℝ (Fin d → ℝ) := (Module.finrank_fin_fun ℝ).symm
    let e1 := ContinuousLinearEquiv.ofFinrankEq hd
    let e2 := (e1.arrowCongr (1 : W ≃L[ℝ] W)).trans (ContinuousLinearEquiv.piRing (Fin d))
    have hc : DifferentiableAt ℝ (fun s ↦ e2 (L s)) t :=
      differentiableAt_pi.mpr fun _ ↦ hL _
    have he := e2.symm.toContinuousLinearMap.differentiableAt.comp t hc
    have heq : (fun s ↦ e2.symm (e2 (L s))) = L := by
      funext s
      exact e2.symm_apply_apply (L s)
    have he' : DifferentiableAt ℝ (fun s ↦ e2.symm (e2 (L s))) t := by
      simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe] using! he
    rwa [heq] at he'
  choose T hT using fun s : ℝ ↦
    (isSmoothCovariantTensor_riemannEvaluation (F.connection s)).1 x
  have hEval (s : ℝ) (a b : E) :
      (F.connection s).curvatureTensor x u a v b = T s ![u, a, v, b] :=
    hT s ![u, a, v, b]
  have hu1 (a b z : E) : Function.update ![u, a, v, b] 1 z = ![u, z, v, b] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have hu3 (a b z : E) : Function.update ![u, a, v, b] 3 z = ![u, a, v, z] := by
    ext i
    fin_cases i <;> simp [Function.update]
  have ha1 (s : ℝ) (a b z : E) : (F.connection s).curvatureTensor x u (a + b) v z =
      (F.connection s).curvatureTensor x u a v z +
        (F.connection s).curvatureTensor x u b v z := by
    simp only [hEval]
    simpa only [hu1] using (T s).map_update_add ![u, a, v, z] 1 a b
  have ha2 (s : ℝ) (a b z : E) : (F.connection s).curvatureTensor x u z v (a + b) =
      (F.connection s).curvatureTensor x u z v a +
        (F.connection s).curvatureTensor x u z v b := by
    simp only [hEval]
    simpa only [hu3] using (T s).map_update_add ![u, z, v, a] 3 a b
  have hs1 (s c : ℝ) (a b : E) : (F.connection s).curvatureTensor x u (c • a) v b =
      c • (F.connection s).curvatureTensor x u a v b := by
    simp only [hEval]
    simpa only [hu1] using (T s).map_update_smul ![u, a, v, b] 1 c a
  have hs2 (s c : ℝ) (a b : E) : (F.connection s).curvatureTensor x u a v (c • b) =
      c • (F.connection s).curvatureTensor x u a v b := by
    simp only [hEval]
    simpa only [hu3] using (T s).map_update_smul ![u, a, v, b] 3 c b
  let R : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ LinearMap.toContinuousLinearMap
    { toFun := fun a ↦ LinearMap.toContinuousLinearMap
        { toFun := fun b ↦ (F.connection s).curvatureTensor x u a v b
          map_add' := fun b c ↦ ha2 s b c a
          map_smul' := fun c b ↦ hs2 s c a b }
      map_add' := by intro a b; ext z; exact ha1 s a b z
      map_smul' := by intro c a; ext b; exact hs1 s c a b }
  let G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ (F.metric s).inner x
  have hRd : DifferentiableAt ℝ R t := by
    apply hclm (V := E) (W := E →L[ℝ] ℝ) (L := R)
    intro a
    apply hclm (V := E) (W := ℝ) (L := fun s ↦ R s a)
    intro b
    exact (hRtime a b).differentiableAt
  have hg (a b : E) : HasDerivAt (fun s ↦ G s a b)
      (-2 * (F.connection t).ricci x a b) t :=
    (F.equation t (interior_subset ht) x a b).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
  have hGd : DifferentiableAt ℝ G t := by
    apply hclm (V := E) (W := E →L[ℝ] ℝ) (L := G)
    intro a
    apply hclm (V := E) (W := ℝ) (L := fun s ↦ G s a)
    intro b
    exact (hg a b).differentiableAt
  have hRtime' : HasDerivAt R (deriv R t) t := hRd.hasDerivAt
  have hGtime : HasDerivAt G (deriv G t) t := hGd.hasDerivAt
  have hR' (a b : E) : deriv R t a b = r a b := by
    have he : HasDerivAt (fun s ↦ R s a b) (deriv R t a b) t := by
      simpa only [map_zero, zero_apply, zero_add, add_zero] using!
        (hRtime'.clm_apply (F := E) (G := E →L[ℝ] ℝ)
          (hasDerivAt_const t a)).clm_apply (F := E) (G := ℝ) (hasDerivAt_const t b)
    exact he.unique (hRtime a b)
  have hG' (a b : E) : deriv G t a b = -2 * (F.connection t).ricci x a b := by
    have he : HasDerivAt (fun s ↦ G s a b) (deriv G t a b) t := by
      simpa only [map_zero, zero_apply, zero_add, add_zero] using!
        (hGtime.clm_apply (F := E) (G := E →L[ℝ] ℝ)
          (hasDerivAt_const t a)).clm_apply (F := E) (G := ℝ) (hasDerivAt_const t b)
    exact he.unique (hg a b)
  let Q := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  let B : ℝ → E →L[ℝ] E := fun s ↦ Q.toContinuousLinearMap.comp (G s)
  let C : ℝ → E →L[ℝ] E := fun s ↦ Q.toContinuousLinearMap.comp (R s)
  let V : E →L[ℝ] E := Q.toContinuousLinearMap.comp (deriv G t)
  have hBd : HasDerivAt B V t := by
    simpa only [ContinuousLinearMap.zero_comp, zero_add, V, B] using!
      (hasDerivAt_const t Q.toContinuousLinearMap).clm_comp hGtime
  have hCd : HasDerivAt C (Q.toContinuousLinearMap.comp (deriv R t)) t := by
    simpa only [ContinuousLinearMap.zero_comp, zero_add, C] using!
      (hasDerivAt_const t Q.toContinuousLinearMap).clm_comp hRtime'
  have hCderiv : deriv C t = Q.toContinuousLinearMap.comp (deriv R t) :=
    HasDerivAt.deriv (𝕜 := ℝ) (F := E →L[ℝ] E) hCd
  have hBt : B t = ContinuousLinearMap.id ℝ E := by
    ext a
    exact (InnerProductSpace.toDual ℝ E).symm_apply_apply a
  have hInv (s : ℝ) : (B s).IsInvertible := by
    have hz (a : E) (ha : B s a = 0) : a = 0 := by
      have hg0 : G s a = 0 := Q.injective (by simpa [B] using ha)
      have hi : (F.metric s).inner x a a = 0 := by
        simpa [G] using congrArg (fun L : E →L[ℝ] ℝ ↦ L a) hg0
      by_contra hne
      exact (ne_of_gt ((F.metric s).pos x a hne)) hi
    have hinj : Function.Injective (B s) := by
      intro a b h
      apply sub_eq_zero.mp
      apply hz
      rw [map_sub, h, sub_self]
    have hsurj : Function.Surjective (B s) := LinearMap.injective_iff_surjective.mp hinj
    exact ⟨(LinearEquiv.ofBijective (B s).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
      by ext a; rfl⟩
  let L : ℝ → E →L[ℝ] E := fun s ↦ (B s).inverse.comp (C s)
  have hLd : DifferentiableAt ℝ L t :=
    (((hInv t).contDiffAt_map_inverse (n := 1)).differentiableAt (by norm_num)
      |>.comp t hBd.differentiableAt).clm_comp hCd.differentiableAt
  have hLtime : HasDerivAt L (deriv L t) t := hLd.hasDerivAt
  have hBL (s : ℝ) (a : E) : B s (L s a) = C s a := (hInv s).self_apply_inverse _
  have hpair (s : ℝ) (a b : E) : (F.metric s).inner x (L s a) b =
      (F.connection s).curvatureTensor x u a v b := by
    have he := Q.injective (hBL s a)
    exact congrArg (fun f : E →L[ℝ] ℝ ↦ f b) he
  have hprod : HasDerivAt C (V.comp (L t) + (B t).comp (deriv L t)) t := by
    have heq : (fun s ↦ (B s).comp (L s)) = C := by
      funext s
      ext a
      exact hBL s a
    simpa only [heq] using hBd.clm_comp (E := E) (F := E) (G := E) hLtime
  have hL' : deriv L t = deriv C t - V.comp (L t) := by
    have he := hprod.unique hCd
    rw [hBt, ContinuousLinearMap.id_comp] at he
    apply eq_sub_iff_add_eq.mpr
    simpa only [hCderiv, add_comm] using he
  have hC'pair (a b : E) : (F.metric t).inner x (deriv C t a) b = r a b := by
    rw [hCderiv]
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (deriv R t a)) b = r a b
    rw [InnerProductSpace.toDual_symm_apply, hR']
  have hVpair (a b : E) : (F.metric t).inner x (V a) b =
      -2 * (F.connection t).ricci x a b := by
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (deriv G t a)) b = _
    rw [InnerProductSpace.toDual_symm_apply, hG']
  let b := (F.metric t).orthonormalBasis x
  have hTrace (s : ℝ) : (∑ i, inner ℝ (b i) (L s (b i))) =
      (F.connection s).ricci x u v := by
    calc
      _ = LinearMap.trace ℝ E (L s).toLinearMap := by
        symm
        rw [LinearMap.trace_eq_matrix_trace ℝ b.toBasis]
        simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply]
        rfl
      _ = ∑ i, (F.metric s).inner x ((F.metric s).orthonormalBasis x i)
          (L s ((F.metric s).orthonormalBasis x i)) := by
        let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
          ⟨(F.metric s).toRiemannianMetric⟩
        rw [LinearMap.trace_eq_matrix_trace ℝ ((F.metric s).orthonormalBasis x).toBasis]
        simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
          OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply]
        rfl
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [(F.metric s).symm, hpair]
  have hExpand (a : E) : L t a =
      ∑ j, (F.connection t).curvatureTensor x u a v (b j) • b j := by
    calc
      _ = ∑ j, inner ℝ (b j) (L t a) • b j := (b.sum_repr' (L t a)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        change (F.metric t).inner x (b j) (L t a) • b j = _
        rw [(F.metric t).symm, hpair]
  have hTerm : (∑ i, inner ℝ (b i) (V.comp (L t) (b i))) =
      -2 * (∑ i, ∑ j, (F.connection t).ricci x (b i) (b j) *
        (F.connection t).curvatureTensor x u (b i) v (b j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ContinuousLinearMap.comp_apply, hExpand (b i), map_sum, map_smul,
      inner_sum, inner_smul_right, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (F.connection t).curvatureTensor x u (b i) v (b j) *
      (F.metric t).inner x (b i) (V (b j)) = _
    rw [(F.metric t).symm, hVpair, ricci_symm (F.connection t) x (b j) (b i)]
    ring
  have hTraceC : (∑ i, inner ℝ (b i) (deriv C t (b i))) = ∑ i, r (b i) (b i) := by
    apply Finset.sum_congr rfl
    intro i _
    change (F.metric t).inner x (b i) (deriv C t (b i)) = _
    rw [(F.metric t).symm, hC'pair]
  have hd : HasDerivAt (fun s ↦ ∑ i, inner ℝ (b i) (L s (b i)))
      (∑ i, inner ℝ (b i) (deriv L t (b i))) t := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [map_zero, zero_apply, zero_add, add_zero] using!
      (hasDerivAt_const t (innerSL ℝ (b i))).clm_apply (F := E) (G := ℝ)
        (hLtime.clm_apply (F := E) (G := E) (hasDerivAt_const t (b i)))
  have hdRic : HasDerivAt (fun s ↦ (F.connection s).ricci x u v)
      (∑ i, inner ℝ (b i) (deriv L t (b i))) t :=
    hd.congr_of_eventuallyEq (Eventually.of_forall fun s ↦ (hTrace s).symm)
  apply hdRic.congr_deriv
  rw [hL']
  simp only [sub_apply, inner_sub_right, Finset.sum_sub_distrib, hTraceC, hTerm]
  ring

end PoincareConjecture.RicciFlowAnalysis

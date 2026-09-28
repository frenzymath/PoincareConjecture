import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Tensors.RicciRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Reaction
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Normed.Module.RCLike.Basic

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Function

universe u

namespace PoincareConjecture.RicciFlowAnalysis

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private noncomputable def twoBilin
    (A : MultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ) : LinearMap.BilinForm ℝ E :=
  (MultilinearMap.ofSubsingleton ℝ E (E →ₗ[ℝ] ℝ) (0 : Fin 1)).symm A.curryRight

private theorem twoBilin_apply (A : MultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ)
    (a b : E) : twoBilin A a b = A ![a, b] := by
  apply congrArg A
  funext i
  fin_cases i <;> rfl

private theorem bilinear_trace {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm ℝ E)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, B (b i) (b i)) = ∑ j, B (c j) (c j) := by
  classical
  calc
    _ = ∑ i, ∑ j, inner ℝ (c j) (b i) * B (b i) (c j) := by
      apply Finset.sum_congr rfl
      intro i hi
      conv_lhs => arg 2; rw [← c.sum_repr' (b i)]
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ j, ∑ i, inner ℝ (c j) (b i) * B (b i) (c j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      have h := congrArg (fun a : E ↦ B a (c j)) (b.sum_repr' (c j))
      simp only [map_sum, LinearMap.sum_apply, map_smul,
        LinearMap.smul_apply, smul_eq_mul] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro i hi
      rw [real_inner_comm (c j) (b i)]

private theorem bilinear_contraction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C B : LinearMap.BilinForm ℝ E)
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
    (∑ i, ∑ j, C (b i) (b j) * B (b i) (b j)) =
      ∑ i, ∑ j, C (c i) (c j) * B (c i) (c j) := by
  classical
  calc
    _ = ∑ j, ∑ i, C (b i) (b j) * B (b i) (b j) := Finset.sum_comm
    _ = ∑ j, ∑ i, C (c i) (b j) * B (c i) (b j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact bilinear_trace
        (LinearMap.BilinForm.linMulLin (C.flip (b j)) (B.flip (b j))) b c
    _ = ∑ i, ∑ j, C (c i) (b j) * B (c i) (b j) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact bilinear_trace (LinearMap.BilinForm.linMulLin (C (c i)) (B (c i))) b c

private noncomputable def curvatureTraceSlice
    (T : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (a c : E) :
    LinearMap.BilinForm ℝ E :=
  twoBilin ((T.curryMid 2 c).curryLeft a)

private theorem curvatureTraceSlice_apply
    (T : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (a b c d : E) :
    curvatureTraceSlice T a c b d = T ![a, b, c, d] := by
  rw [curvatureTraceSlice, twoBilin_apply]
  apply congrArg T
  funext i
  fin_cases i <;> rfl

private noncomputable def curvatureInputSlice
    (T : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (b d : E) :
    LinearMap.BilinForm ℝ E :=
  twoBilin ((T.curryMid 3 d).curryMid 1 b)

private theorem curvatureInputSlice_apply
    (T : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (a b c d : E) :
    curvatureInputSlice T b d a c = T ![a, b, c, d] := by
  rw [curvatureInputSlice, twoBilin_apply]
  apply congrArg T
  funext i
  fin_cases i <;> rfl

private noncomputable def reactionBilin {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)
    (B : LinearMap.BilinForm ℝ E) : LinearMap.BilinForm ℝ E :=
  (2 : ℝ) • (∑ i, ∑ j, B (b i) (b j) • curvatureInputSlice T (b i) (b j)) -
    (2 : ℝ) • ∑ i, LinearMap.BilinForm.linMulLin (B.flip (b i)) (B (b i))

private theorem reactionBilin_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)
    (B : LinearMap.BilinForm ℝ E) (a c : E) :
    reactionBilin b T B a c =
      2 * (∑ i, ∑ j, T ![a, b i, c, b j] * B (b i) (b j)) -
        2 * (∑ i, B a (b i) * B (b i) c) := by
  classical
  simp only [reactionBilin, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.BilinForm.linMulLin_apply,
    curvatureInputSlice_apply, smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

end Algebra

set_option maxHeartbeats 800000 in

private theorem frame_reaction_identity
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (B : Fin 3 → Fin 3 → ℝ)
    (epsilon : ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hsymm : ∀ a b, B a b = B b a)
    (htrace : ∀ a b, B a b = ∑ i, R a i b i)
    (h00 : B 0 0 = -epsilon) (h01 : B 0 1 = 0) (h02 : B 0 2 = 0) :
    2 * (∑ i, ∑ j, R 0 i 0 j * B i j) - 2 * (∑ i, B 0 i * B i 0) -
      2 * epsilon * B 0 0 + epsilon * ((∑ i, B i i) + epsilon) =
        (B 1 1 - B 2 2) ^ 2 + 4 * (B 1 2) ^ 2 := by
  have hf (a c d) : R a a c d = 0 := by linarith only [hfirst a a c d]
  have hl (a b c) : R a b c c = 0 := by linarith only [hlast a b c c]
  have hrev (a b) : R b a b a = R a b a b := by
    rw [hfirst b a b a, hlast a b b a, neg_neg]
  have hd0 := htrace 0 0
  have hd1 := htrace 1 1
  have hd2 := htrace 2 2
  have hc := htrace 1 2
  norm_num [Fin.sum_univ_succ, hf, hl] at hd0 hd1 hd2 hc
  rw [h00] at hd0
  rw [hrev 0 1] at hd1
  rw [hrev 0 2, hrev 1 2] at hd2
  have hRa : R 0 1 0 1 = (-epsilon + B 1 1 - B 2 2) / 2 := by
    linarith only [hd0, hd1, hd2]
  have hRb : R 0 2 0 2 = (-epsilon + B 2 2 - B 1 1) / 2 := by
    linarith only [hd0, hd1, hd2]
  have hRc : R 0 1 0 2 = B 1 2 := by
    rw [hfirst 1 0 2 0, hlast 0 1 2 0, neg_neg] at hc
    exact hc.symm
  have hRd : R 0 2 0 1 = B 1 2 := (hpair 0 2 0 1).trans hRc
  norm_num [Fin.sum_univ_succ, hf, hl, h00, h01, h02,
    hRa, hRb, hRc, hRd, hsymm 2 1]
  ring

set_option maxHeartbeats 1200000 in

private theorem shifted_reaction_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (T : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ) (B : LinearMap.BilinForm ℝ E)
    (hdim : Module.finrank ℝ E = 3)
    (hfirst : ∀ a b c d, T ![a, b, c, d] = -T ![b, a, c, d])
    (hlast : ∀ a b c d, T ![a, b, c, d] = -T ![a, b, d, c])
    (hpair : ∀ a b c d, T ![a, b, c, d] = T ![c, d, a, b])
    (hsymm : ∀ a c, B a c = B c a)
    (htrace : ∀ a c, B a c = ∑ i, T ![a, b i, c, b i])
    (epsilon : ℝ) (hshift : ∀ a, 0 ≤ B a a + epsilon * inner ℝ a a)
    (u : E) (hnull : B u u + epsilon * inner ℝ u u = 0) :
    -epsilon * ((∑ i, B (b i) (b i)) + epsilon) * inner ℝ u u ≤
      reactionBilin b T B u u - 2 * epsilon * B u u := by
  classical
  by_cases hu : u = 0
  · subst u
    simp
  let S : LinearMap.BilinForm ℝ E := B + epsilon • innerₗ E
  have hSsymm : S.IsSymm := ⟨fun a c ↦ by
    change B a c + epsilon * inner ℝ a c = B c a + epsilon * inner ℝ c a
    rw [hsymm a c, real_inner_comm a c]⟩
  have hSpos (a : E) : 0 ≤ S a a := hshift a
  have hSnull : S u u = 0 := hnull
  have hkernel : S u = 0 := LinearMap.mem_ker.mp
    ((S.apply_apply_same_eq_zero_iff hSpos
      (LinearMap.BilinForm.isSymm_iff.mp hSsymm)).mp hSnull)
  let v0 : E := ‖u‖⁻¹ • u
  have hv0 : ‖v0‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
  have hon : Orthonormal ℝ
      (({0} : Set (Fin 3)).domRestrict (fun _ : Fin 3 ↦ v0)) := by
    let : Subsingleton ↥({0} : Set (Fin 3)) := Set.subsingleton_singleton.coe_sort
    exact ⟨fun _ ↦ hv0, Subsingleton.pairwise⟩
  obtain ⟨e, he⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := E) (ι := Fin 3) (v := fun _ ↦ v0) (s := {0})
    (by simpa using hdim) hon
  have he0 : e 0 = ‖u‖⁻¹ • u := he 0 (Set.mem_singleton 0)
  have hscale : ‖u‖ • e 0 = u := by
    rw [he0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
  have hekernel : S (e 0) = 0 := by rw [he0, map_smul, hkernel, smul_zero]
  have hrow (i : Fin 3) :
      B (e 0) (e i) = -epsilon * (if (0 : Fin 3) = i then 1 else 0) := by
    have h := congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L (e i)) hekernel
    change B (e 0) (e i) + epsilon * inner ℝ (e 0) (e i) = 0 at h
    rw [e.inner_eq_ite] at h
    linarith only [h]
  have htrace_e (a c : E) : B a c = ∑ i, T ![a, e i, c, e i] := by
    calc
      _ = ∑ i, curvatureTraceSlice T a c (b i) (b i) := by
        simpa only [curvatureTraceSlice_apply] using htrace a c
      _ = ∑ i, curvatureTraceSlice T a c (e i) (e i) :=
        bilinear_trace (curvatureTraceSlice T a c) b e
      _ = _ := by simp only [curvatureTraceSlice_apply]
  have hscalar : (∑ i, B (b i) (b i)) = ∑ i, B (e i) (e i) := bilinear_trace B b e
  have hQ : reactionBilin b T B (e 0) (e 0) =
      2 * (∑ i, ∑ j, T ![e 0, e i, e 0, e j] * B (e i) (e j)) -
        2 * (∑ i, B (e 0) (e i) * B (e i) (e 0)) := by
    rw [reactionBilin_apply]
    have hC := bilinear_contraction (curvatureTraceSlice T (e 0) (e 0)) B b e
    simp only [curvatureTraceSlice_apply] at hC
    have hSq := bilinear_trace
      (LinearMap.BilinForm.linMulLin (B (e 0)) (B.flip (e 0))) b e
    exact congrArg₂ (fun a c : ℝ ↦ 2 * a - 2 * c) hC hSq
  have hframe := frame_reaction_identity
    (fun i j k l ↦ T ![e i, e j, e k, e l]) (fun i j ↦ B (e i) (e j)) epsilon
    (fun i j k l ↦ hfirst (e i) (e j) (e k) (e l))
    (fun i j k l ↦ hlast (e i) (e j) (e k) (e l))
    (fun i j k l ↦ hpair (e i) (e j) (e k) (e l))
    (fun i j ↦ hsymm (e i) (e j)) (fun i j ↦ htrace_e (e i) (e j))
    (by simpa using hrow 0) (by simpa using hrow 1) (by simpa using hrow 2)
  have hnon : 0 ≤ reactionBilin b T B (e 0) (e 0) - 2 * epsilon * B (e 0) (e 0) +
      epsilon * ((∑ i, B (b i) (b i)) + epsilon) := by
    rw [hQ, hscalar, hframe]
    positivity
  have hscaleEval (L : LinearMap.BilinForm ℝ E) :
      L u u = ‖u‖ ^ 2 * L (e 0) (e 0) := by
    calc
      _ = L (‖u‖ • e 0) (‖u‖ • e 0) :=
        congrArg₂ (fun a c : E ↦ L a c) hscale.symm hscale.symm
      _ = _ := by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
  rw [hscaleEval B, hscaleEval (reactionBilin b T B), real_inner_self_eq_norm_sq]
  have hscaled := mul_nonneg (sq_nonneg ‖u‖) hnon
  nlinarith only [hscaled]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem ricciReaction_lower_bound_of_shiftedRicci_null
    (D : LeviCivitaData g) (x : M) (epsilon : ℝ)
    (hshift : ∀ v : TangentSpace (𝓡 3) x,
      0 ≤ D.ricci x v v + epsilon * g.inner x v v)
    (u : TangentSpace (𝓡 3) x)
    (hnull : D.ricci x u u + epsilon * g.inner x u u = 0) :
    -epsilon * (D.scalarCurvature x + epsilon) * g.inner x u u ≤
      D.ricciReaction x u u - 2 * epsilon * D.ricci x u u := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := TangentSpace (𝓡 3) x
  let : FiniteDimensional ℝ E := VectorBundle.finiteDimensional ℝ
    (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3) : M → Type _) x
  let b := g.orthonormalBasis x
  obtain ⟨T, hT⟩ := (isSmoothCovariantTensor_riemannEvaluation D).1 x
  obtain ⟨A, hA⟩ := (isSmoothCovariantTensor_ricciEvaluation D).1 x
  let B : LinearMap.BilinForm ℝ E := twoBilin A
  have hR (a b c d : E) : T ![a, b, c, d] = D.curvatureTensor x a b c d :=
    (hT ![a, b, c, d]).symm
  have hB (a c : E) : B a c = D.ricci x a c :=
    (twoBilin_apply A a c).trans (hA ![a, c]).symm
  have hinner (a c : E) : inner ℝ a c = g.inner x a c := rfl
  have hdim : Module.finrank ℝ E = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  have hfirst (a b c d : E) : T ![a, b, c, d] = -T ![b, a, c, d] := by
    simpa only [hR] using curvatureTensor_swap_first D x b a c d
  have hlast (a b c d : E) : T ![a, b, c, d] = -T ![a, b, d, c] := by
    simpa only [hR] using curvatureTensor_swap_last D x a b c d
  have hpair (a b c d : E) : T ![a, b, c, d] = T ![c, d, a, b] := by
    simpa only [hR] using curvatureTensor_pair_exchange D x a b c d
  have hsymm (a c : E) : B a c = B c a := by simpa only [hB] using ricci_symm D x a c
  have htrace (a c : E) : B a c = ∑ i, T ![a, b i, c, b i] := by
    simp only [hB, hR]
    rfl
  have hactual : reactionBilin b T B u u = D.ricciReaction x u u := by
    rw [reactionBilin_apply]
    change 2 * (∑ i, ∑ j, T ![u, b i, u, b j] * B (b i) (b j)) -
      2 * (∑ i, B u (b i) * B (b i) u) =
        2 * (∑ i, ∑ j, D.curvatureTensor x u (b i) u (b j) * D.ricci x (b i) (b j)) -
          2 * (∑ i, D.ricci x u (b i) * D.ricci x (b i) u)
    apply congrArg₂ (fun a c : ℝ ↦ 2 * a - 2 * c)
    · apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact congrArg₂ (fun a c : ℝ ↦ a * c) (hR u (b i) u (b j)) (hB (b i) (b j))
    · apply Finset.sum_congr rfl
      intro i hi
      exact congrArg₂ (fun a c : ℝ ↦ a * c) (hB u (b i)) (hB (b i) u)
  have hscalar : (∑ i, B (b i) (b i)) = D.scalarCurvature x := by
    simp only [hB]
    rfl
  have h := shifted_reaction_bound b T B hdim hfirst hlast hpair hsymm htrace epsilon
    (fun a ↦ by rw [hB a a, hinner a a]; exact hshift a) u
    (by rw [hB u u, hinner u u]; exact hnull)
  calc
    _ = -epsilon * ((∑ i, B (b i) (b i)) + epsilon) * inner ℝ u u := by
      rw [hscalar, hinner u u]
    _ ≤ reactionBilin b T B u u - 2 * epsilon * B u u := h
    _ = _ := by rw [hactual, hB u u]

theorem ricciReaction_nonneg_of_nonnegativeRicciAt_null
    (D : LeviCivitaData g) (x : M)
    (hRic : ∀ v : TangentSpace (𝓡 3) x, 0 ≤ D.ricci x v v)
    (u : TangentSpace (𝓡 3) x) (hu : D.ricci x u u = 0) :
    0 ≤ D.ricciReaction x u u := by
  simpa only [neg_zero, zero_mul, mul_zero, sub_zero] using
    ricciReaction_lower_bound_of_shiftedRicci_null D x 0
      (fun v ↦ by simpa only [zero_mul, add_zero] using hRic v) u
      (by simpa only [zero_mul, add_zero] using hu)

end PoincareConjecture.RicciFlowAnalysis

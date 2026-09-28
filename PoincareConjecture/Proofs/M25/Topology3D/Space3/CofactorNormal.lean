import PoincareConjecture.Proofs.M25.Topology3D.Services
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CrossCofactor
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLin














set_option autoImplicit false

open Set Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Elementwise

namespace PoincareConjecture.M25.Topology3D


noncomputable def cofactorNormalMatrix (A : E3 →L[ℝ] E3) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix (PiLp.basisFun 2 ℝ (Fin 3))
    (PiLp.basisFun 2 ℝ (Fin 3)) A.toLinearMap


noncomputable def cofactorNormal (A : E3 →L[ℝ] E3) (p : E3) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    ((cofactorNormalMatrix A).adjugate.transpose *ᵥ
      (EuclideanSpace.equiv (Fin 3) ℝ) p)

private theorem cofactorNormalMatrix_mulVec (A : E3 →L[ℝ] E3) (v : E3) :
    cofactorNormalMatrix A *ᵥ (EuclideanSpace.equiv (Fin 3) ℝ) v =
      (EuclideanSpace.equiv (Fin 3) ℝ) (A v) := by
  exact A.toLinearMap.toMatrix_mulVec_repr
    (PiLp.basisFun 2 ℝ (Fin 3)) (PiLp.basisFun 2 ℝ (Fin 3)) v


theorem cofactorNormal_smul (A : E3 →L[ℝ] E3) (r : ℝ) (p : E3) :
    cofactorNormal A (r • p) = r • cofactorNormal A p := by
  simp only [cofactorNormal, map_smul, Matrix.mulVec_smul]


theorem contDiff_cofactorNormal :
    ContDiff ℝ ∞ (fun z : (E3 →L[ℝ] E3) × E3 => cofactorNormal z.1 z.2) := by
  have hM : ContDiff ℝ ∞ cofactorNormalMatrix := by
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    simp only [cofactorNormalMatrix, LinearMap.toMatrix_apply, PiLp.basisFun_repr]
    have hEval : ContDiff ℝ ∞ (fun A : E3 →L[ℝ] E3 =>
        A ((PiLp.basisFun 2 ℝ (Fin 3)) j)) :=
      contDiff_id.clm_apply contDiff_const
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hEval
  have hpair : ContDiff ℝ ∞ (fun z : (E3 →L[ℝ] E3) × E3 =>
      (cofactorNormalMatrix z.1, (EuclideanSpace.equiv (Fin 3) ℝ) z.2)) :=
    (hM.comp contDiff_fst).prodMk
      ((EuclideanSpace.equiv (Fin 3) ℝ).contDiff.comp contDiff_snd)
  have hcof := contDiff_adjugate_transpose_mulVec.comp hpair
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp hcof

private noncomputable def normalCross (v w : E3) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm
    (crossProduct ((EuclideanSpace.equiv (Fin 3) ℝ) v)
      ((EuclideanSpace.equiv (Fin 3) ℝ) w))

private theorem normalCross_inner_left (v w : E3) :
    ⟪normalCross v w, v⟫_ℝ = 0 := by
  change WithLp.ofLp v ⬝ᵥ star
    (crossProduct (WithLp.ofLp v) (WithLp.ofLp w)) = 0
  simpa only [star_trivial] using dot_self_cross (WithLp.ofLp v) (WithLp.ofLp w)

private theorem normalCross_inner_right (v w : E3) :
    ⟪normalCross v w, w⟫_ℝ = 0 := by
  change WithLp.ofLp w ⬝ᵥ star
    (crossProduct (WithLp.ofLp v) (WithLp.ofLp w)) = 0
  simpa only [star_trivial] using dot_cross_self (WithLp.ofLp v) (WithLp.ofLp w)

private theorem normalCross_ne_zero {v w : E3}
    (h : LinearIndependent ℝ ![v, w]) : normalCross v w ≠ 0 := by
  let e := EuclideanSpace.equiv (Fin 3) ℝ
  have hi := h.map' e.toLinearEquiv.toLinearMap
    (LinearMap.ker_eq_bot_of_injective e.injective)
  have hi' : LinearIndependent ℝ ![e v, e w] := by
    convert! hi using 1
    ext i
    fin_cases i <;> rfl
  have hc := crossProduct_ne_zero_iff_linearIndependent.mpr hi'
  intro hz
  apply hc
  have hh := congrArg e hz
  simpa only [normalCross, e, ContinuousLinearEquiv.apply_symm_apply, map_zero] using hh

private theorem normalCross_map (A : E3 →L[ℝ] E3) (v w : E3) :
    normalCross (A v) (A w) = cofactorNormal A (normalCross v w) := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
  simp only [normalCross, cofactorNormal, ContinuousLinearEquiv.apply_symm_apply]
  rw [← cofactorNormalMatrix_mulVec A v, ← cofactorNormalMatrix_mulVec A w]
  exact mulVec_crossProduct_cofactor _ _ _

private theorem inner_map_eq_zero_of_plane_basis
    (P : Submodule ℝ E3) (b : OrthonormalBasis (Fin 2) ℝ P)
    (A : E3 →L[ℝ] E3) (n : E3)
    (h0 : ⟪n, A (b 0 : E3)⟫_ℝ = 0) (h1 : ⟪n, A (b 1 : E3)⟫_ℝ = 0)
    (x : P) : ⟪n, A (x : E3)⟫_ℝ = 0 := by
  have hx : A (x : E3) =
      b.repr x 0 • A (b 0 : E3) + b.repr x 1 • A (b 1 : E3) := by
    have hh := congrArg (fun y : P => A (y : E3)) (b.sum_repr x)
    simpa only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul,
      map_add, map_smul] using hh.symm
  rw [hx, inner_add_right, inner_smul_right, inner_smul_right, h0, h1,
    mul_zero, mul_zero, add_zero]

private theorem plane_basis_pair_independent
    (P : Submodule ℝ E3) (b : OrthonormalBasis (Fin 2) ℝ P)
    (A : E3 →L[ℝ] E3) (hA : Set.InjOn A (P : Set E3)) :
    LinearIndependent ℝ ![A (b 0 : E3), A (b 1 : E3)] := by
  let f : P →ₗ[ℝ] E3 := A.toLinearMap.comp P.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (hA x.property y.property hxy)
  have hi := b.toBasis.linearIndependent.map' f
    (LinearMap.ker_eq_bot_of_injective hf)
  convert! hi using 1
  ext i
  fin_cases i <;> rfl



theorem cofactorNormal_nonzero_orthogonal (A : E3 →L[ℝ] E3) (p : E3)
    (hp : ‖p‖ = 1) (hAp : A p = 0)
    (hA : Set.InjOn A ((ℝ ∙ p)ᗮ : Set E3)) :
    cofactorNormal A p ≠ 0 ∧ ∀ v : E3, ⟪cofactorNormal A p, A v⟫_ℝ = 0 := by
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  have hp0 : p ≠ 0 := by
    intro hz
    simp only [hz, norm_zero, zero_ne_one] at hp
  let P : Submodule ℝ E3 := (ℝ ∙ p)ᗮ
  let b : OrthonormalBasis (Fin 2) ℝ P :=
    OrthonormalBasis.fromOrthogonalSpanSingleton 2 hp0
  let a : E3 := b 0
  let d : E3 := b 1
  have had : LinearIndependent ℝ ![a, d] :=
    plane_basis_pair_independent P b (ContinuousLinearMap.id ℝ E3)
      (fun _ _ _ _ h => h)
  have hc0 : normalCross a d ≠ 0 := normalCross_ne_zero had
  have hcP : normalCross a d ∈ Pᗮ := by
    apply (P.mem_orthogonal' _).mpr
    intro x hx
    exact inner_map_eq_zero_of_plane_basis P b (ContinuousLinearMap.id ℝ E3)
      (normalCross a d) (normalCross_inner_left a d)
      (normalCross_inner_right a d) ⟨x, hx⟩
  have hcspan : normalCross a d ∈ ℝ ∙ p := by
    simpa only [P, Submodule.orthogonal_orthogonal] using hcP
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hcspan
  have hk0 : k ≠ 0 := by
    intro hz
    apply hc0
    simpa only [hz, zero_smul] using hk.symm
  have hAd0 : normalCross (A a) (A d) ≠ 0 :=
    normalCross_ne_zero (plane_basis_pair_independent P b A hA)
  have hcross : normalCross (A a) (A d) = k • cofactorNormal A p := by
    rw [normalCross_map, ← hk, cofactorNormal_smul]
  refine ⟨?_, ?_⟩
  · intro hn
    apply hAd0
    rw [hcross, hn, smul_zero]
  · intro v
    have hpp : ⟪p, p⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_mul_norm, hp, one_mul]
    have hvP : v - ⟪p, v⟫_ℝ • p ∈ P := by
      apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      rw [inner_sub_right, inner_smul_right, hpp, mul_one, sub_self]
    have hAv : A (v - ⟪p, v⟫_ℝ • p) = A v := by
      rw [map_sub, map_smul, hAp, smul_zero, sub_zero]
    have hi := inner_map_eq_zero_of_plane_basis P b A (normalCross (A a) (A d))
      (normalCross_inner_left (A a) (A d)) (normalCross_inner_right (A a) (A d))
      ⟨v - ⟪p, v⟫_ℝ • p, hvP⟩
    change ⟪normalCross (A a) (A d), A (v - ⟪p, v⟫_ℝ • p)⟫_ℝ = 0 at hi
    rw [hAv, hcross, real_inner_smul_left] at hi
    exact (mul_eq_zero.mp hi).resolve_left hk0

end PoincareConjecture.M25.Topology3D

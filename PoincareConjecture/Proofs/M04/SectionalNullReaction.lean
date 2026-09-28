import PoincareConjecture.Proofs.M04.RicciRegularity
import PoincareConjecture.Proofs.M04.CurvatureSymmetries
import PoincareConjecture.Definitions.Ch03.CurvatureReaction
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Normed.Module.RCLike.Basic








set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Function

universe u

namespace PoincareConjecture.M04

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "Four" => MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ
local notation "Bilin" => LinearMap.BilinForm ℝ E

private noncomputable def twoBilin
    (A : MultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ) : Bilin :=
  (MultilinearMap.ofSubsingleton ℝ E (E →ₗ[ℝ] ℝ) (0 : Fin 1)).symm A.curryRight

private theorem twoBilin_apply (A : MultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ)
    (a b : E) : twoBilin A a b = A ![a, b] := by
  apply congrArg A
  funext i
  fin_cases i <;> rfl

private theorem bilinear_trace {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Bilin) (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
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
    (C B : Bilin) (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E) :
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

private noncomputable def traceSlice (T : Four) (a c : E) : Bilin :=
  twoBilin ((T.curryMid 2 c).curryLeft a)

private theorem traceSlice_apply (T : Four) (a b c d : E) :
    traceSlice T a c b d = T ![a, b, c, d] := by
  rw [traceSlice, twoBilin_apply]
  apply congrArg T
  funext i
  fin_cases i <;> rfl

private noncomputable def inputSlice (T : Four) (b d : E) : Bilin :=
  twoBilin ((T.curryMid 3 d).curryMid 1 b)

private theorem inputSlice_apply (T : Four) (a b c d : E) :
    inputSlice T b d a c = T ![a, b, c, d] := by
  rw [inputSlice, twoBilin_apply]
  apply congrArg T
  funext i
  fin_cases i <;> rfl

private noncomputable def productFour (B C : Bilin) : Four :=
  MultilinearMap.mk' (fun v ↦ B (v 0) (v 1) * C (v 2) (v 3))
    (by
      intro v i a b
      fin_cases i <;>
        simp [Function.update, map_add, LinearMap.add_apply, add_mul, mul_add])
    (by
      intro v i s a
      fin_cases i <;>
        simp [Function.update, map_smul, LinearMap.smul_apply, smul_eq_mul] <;> ring)

private def cycleLast : Equiv.Perm (Fin 4) :=
  (Equiv.swap 2 3).trans (Equiv.swap 1 3)

private noncomputable def gramFour (B C : Bilin) : Four :=
  (productFour B C).domDomCongr (Equiv.swap 1 2) -
    (productFour B C).domDomCongr cycleLast

private theorem gramFour_apply (B C : Bilin) (a b c d : E) :
    gramFour B C ![a, b, c, d] = B a c * C b d - B a d * C b c := by
  simp [gramFour, productFour, cycleLast, Equiv.swap_apply_def]

private noncomputable def curvatureBFour {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) : Four :=
  ∑ i, ∑ j, productFour (inputSlice T (b i) (b j)) (inputSlice T (b i) (b j))

private theorem curvatureBFour_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (a c d f : E) :
    curvatureBFour b T ![a, c, d, f] =
      ∑ i, ∑ j, T ![a, b i, c, b j] * T ![d, b i, f, b j] := by
  simp only [curvatureBFour, sum_apply, productFour,
    MultilinearMap.mk'_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, inputSlice_apply]

private noncomputable def raiseBilin {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (B : Bilin) : E →ₗ[ℝ] E :=
  ∑ i, (B.flip (b i)).smulRight (b i)

private theorem raiseBilin_inner {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (B : Bilin) (a c : E) :
    inner ℝ c (raiseBilin b B a) = B a c := by
  classical
  have h := congrArg (B a) (b.sum_repr' c)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  rw [← h]
  simp only [raiseBilin, LinearMap.sum_apply, LinearMap.smulRight_apply,
    inner_sum, inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm c (b i)]
  change B a (b i) * inner ℝ c (b i) = inner ℝ c (b i) * B a (b i)
  ring

private noncomputable def inputFour (T : Four) (L : E →ₗ[ℝ] E) (i : Fin 4) : Four :=
  T.compLinearMap fun j ↦ if j = i then L else LinearMap.id

private theorem inputFour_apply (T : Four) (L : E →ₗ[ℝ] E)
    (i : Fin 4) (v : Fin 4 → E) :
    inputFour T L i v = T (Function.update v i (L (v i))) := by
  classical
  apply congrArg T
  funext j
  by_cases h : j = i <;> simp [Function.update, h]

private theorem inputFour_sum (T : Four) (L : E →ₗ[ℝ] E) (a c d f : E) :
    (∑ i, inputFour T L i ![a, c, d, f]) =
      T ![L a, c, d, f] + T ![a, L c, d, f] + T ![a, c, L d, f] + T ![a, c, d, L f] := by
  have hv (i : Fin 4) : Function.update ![a, c, d, f] i (L (![a, c, d, f] i)) =
      ![if i = 0 then L a else a, if i = 1 then L c else c,
        if i = 2 then L d else d, if i = 3 then L f else f] := by
    funext j
    fin_cases i <;> fin_cases j <;> simp [Function.update]
  simp only [inputFour_apply, Fin.sum_univ_succ, hv]
  norm_num [Fin.ext_iff]
  ring

private theorem inputFour_raise {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (B : Bilin)
    (k : Fin 4) (v : Fin 4 → E) :
    inputFour T (raiseBilin b B) k v =
      ∑ i, B (v k) (b i) * T (Function.update v k (b i)) := by
  have hraise (a : E) : raiseBilin b B a = ∑ i, B a (b i) • b i := by
    simp only [raiseBilin, LinearMap.sum_apply, LinearMap.smulRight_apply]
    rfl
  rw [inputFour_apply, hraise]
  change (T.toLinearMap v k) (∑ i, B (v k) (b i) • b i) = _
  simp only [map_sum, map_smul, smul_eq_mul, MultilinearMap.toLinearMap_apply]

private theorem raised_corrections {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (B : Bilin) (a c d f : E) :
    T ![raiseBilin b B a, c, d, f] + T ![a, raiseBilin b B c, d, f] +
      T ![a, c, raiseBilin b B d, f] + T ![a, c, d, raiseBilin b B f] =
      ∑ i, (B a (b i) * T ![b i, c, d, f] + B c (b i) * T ![a, b i, d, f] +
        B d (b i) * T ![a, c, b i, f] + B f (b i) * T ![a, c, d, b i]) := by
  rw [← inputFour_sum]
  simp only [inputFour_raise]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hv (k : Fin 4) : Function.update ![a, c, d, f] k (b i) =
      ![if k = 0 then b i else a, if k = 1 then b i else c,
        if k = 2 then b i else d, if k = 3 then b i else f] := by
    funext j
    fin_cases k <;> fin_cases j <;> simp [Function.update]
  simp only [Fin.sum_univ_succ, hv]
  norm_num [Fin.ext_iff, Matrix.cons_val]
  rw [show (![a, c, d, f] : Fin 4 → E) 2 = d from rfl,
    show (![c, d, f] : Fin 3 → E) 2 = f from rfl]
  ring

private noncomputable def reactionFour {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (B : Bilin) : Four :=
  let K := curvatureBFour b T
  (2 : ℝ) • (K - K.domDomCongr (Equiv.swap 2 3) - K.domDomCongr cycleLast +
    K.domDomCongr (Equiv.swap 1 2)) - ∑ i, inputFour T (raiseBilin b B) i

private theorem reactionFour_apply {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (B : Bilin) (a c d f : E) :
    reactionFour b T B ![a, c, d, f] =
      2 * (curvatureBFour b T ![a, c, d, f] - curvatureBFour b T ![a, c, f, d] -
        curvatureBFour b T ![a, f, c, d] + curvatureBFour b T ![a, d, c, f]) -
      (T ![raiseBilin b B a, c, d, f] + T ![a, raiseBilin b B c, d, f] +
        T ![a, c, raiseBilin b B d, f] + T ![a, c, d, raiseBilin b B f]) := by
  classical
  have h23 : (fun i : Fin 4 ↦ (![a, c, d, f] : Fin 4 → E) ((Equiv.swap 2 3) i)) =
      ![a, c, f, d] := by funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have hcyc : (fun i : Fin 4 ↦ (![a, c, d, f] : Fin 4 → E) (cycleLast i)) =
      ![a, f, c, d] := by funext i; fin_cases i <;> simp [cycleLast, Equiv.swap_apply_def]
  have h12 : (fun i : Fin 4 ↦ (![a, c, d, f] : Fin 4 → E) ((Equiv.swap 1 2) i)) =
      ![a, d, c, f] := by funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  simp only [reactionFour, sub_apply, add_apply,
    smul_apply, sum_apply,
    MultilinearMap.domDomCongr_apply, smul_eq_mul]
  rw [h23, hcyc, h12, inputFour_sum]

private theorem curvatureBFour_pair {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (a c d f : E) :
    curvatureBFour b T ![a, c, d, f] = curvatureBFour b T ![d, f, a, c] := by
  simp only [curvatureBFour_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

private theorem curvatureBFour_swap {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four)
    (hpair : ∀ a c d f, T ![a, c, d, f] = T ![d, f, a, c]) (a c d f : E) :
    curvatureBFour b T ![c, a, d, f] = curvatureBFour b T ![a, c, f, d] := by
  rw [curvatureBFour_apply, curvatureBFour_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hpair c (b j) a (b i), hpair d (b j) f (b i)]

private theorem reactionFour_first {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (B : Bilin)
    (hfirst : ∀ a c d f, T ![a, c, d, f] = -T ![c, a, d, f])
    (hpair : ∀ a c d f, T ![a, c, d, f] = T ![d, f, a, c]) (a c d f : E) :
    reactionFour b T B ![a, c, d, f] = -reactionFour b T B ![c, a, d, f] := by
  rw [reactionFour_apply, reactionFour_apply]
  rw [curvatureBFour_swap b T hpair a c d f,
    curvatureBFour_swap b T hpair a c f d,
    curvatureBFour_pair b T c f a d, curvatureBFour_pair b T c d a f]
  rw [hfirst (raiseBilin b B c) a d f, hfirst c (raiseBilin b B a) d f,
    hfirst c a (raiseBilin b B d) f, hfirst c a d (raiseBilin b B f)]
  ring

private theorem reactionFour_last {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (B : Bilin)
    (hlast : ∀ a c d f, T ![a, c, d, f] = -T ![a, c, f, d]) (a c d f : E) :
    reactionFour b T B ![a, c, d, f] = -reactionFour b T B ![a, c, f, d] := by
  rw [reactionFour_apply, reactionFour_apply]
  rw [hlast (raiseBilin b B a) c f d, hlast a (raiseBilin b B c) f d,
    hlast a c (raiseBilin b B f) d, hlast a c f (raiseBilin b B d)]
  ring

private theorem gramFour_first (B : Bilin) (a b c d : E) :
    gramFour B B ![a, b, c, d] = -gramFour B B ![b, a, c, d] := by
  rw [gramFour_apply, gramFour_apply]
  ring

private theorem gramFour_last (B C : Bilin) (a b c d : E) :
    gramFour B C ![a, b, c, d] = -gramFour B C ![a, b, d, c] := by
  rw [gramFour_apply, gramFour_apply]
  ring

private theorem gramFour_sum_first (B C : Bilin) (a b c d : E) :
    (gramFour B C + gramFour C B) ![a, b, c, d] =
      -(gramFour B C + gramFour C B) ![b, a, c, d] := by
  simp only [add_apply, gramFour_apply]
  ring

private theorem sectional_scale (T : Four)
    (hfirst : ∀ a b c d, T ![a, b, c, d] = -T ![b, a, c, d])
    (hlast : ∀ a b c d, T ![a, b, c, d] = -T ![a, b, d, c])
    (a c : E) (r s beta : ℝ) :
    T ![r • a, beta • a + s • c, r • a, beta • a + s • c] =
      r ^ 2 * s ^ 2 * T ![a, c, a, c] := by
  have hf (p q z : E) : T ![p, p, q, z] = 0 := by
    linarith only [hfirst p p q z]
  have hl (p q z : E) : T ![p, q, z, z] = 0 := by
    linarith only [hlast p q z z]
  calc
    _ = r ^ 2 * T ![a, beta • a + s • c, a, beta • a + s • c] := by
      rw [← inputSlice_apply, ← inputSlice_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    _ = _ := by
      rw [← traceSlice_apply]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, traceSlice_apply, hf, hl]
      ring

set_option maxHeartbeats 800000 in

private theorem sectional_nonneg_of_frame [FiniteDimensional ℝ E]
    (S W : Four) (hdim : Module.finrank ℝ E = 3)
    (hSfirst : ∀ a b c d, S ![a, b, c, d] = -S ![b, a, c, d])
    (hSlast : ∀ a b c d, S ![a, b, c, d] = -S ![a, b, d, c])
    (hWfirst : ∀ a b c d, W ![a, b, c, d] = -W ![b, a, c, d])
    (hWlast : ∀ a b c d, W ![a, b, c, d] = -W ![a, b, d, c])
    (hframe : ∀ e : OrthonormalBasis (Fin 3) ℝ E,
      S ![e 0, e 1, e 0, e 1] = 0 → 0 ≤ W ![e 0, e 1, e 0, e 1])
    (u v : E) (hnull : S ![u, v, u, v] = 0) : 0 ≤ W ![u, v, u, v] := by
  classical
  by_cases hu : u = 0
  · subst u
    rw [← inputSlice_apply]
    simp
  let r := ‖u‖
  let a : E := r⁻¹ • u
  have ha : ‖a‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
  have hus : u = r • a := by
    simp [a, r, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu)]
  let beta := inner ℝ a v
  let w : E := v - beta • a
  have hv : v = beta • a + w := by dsimp only [w]; abel
  have haw : inner ℝ a w = 0 := by
    simp [w, beta, inner_sub_right, inner_smul_right, ha]
  by_cases hw : w = 0
  · have hvs : v = beta • a + (0 : ℝ) • (0 : E) := by simpa [hw] using hv
    have h := sectional_scale W hWfirst hWlast a 0 r 0 beta
    have heval := congrArg₂ (fun p q ↦ W ![p, q, p, q]) hus hvs
    rw [heval, h]
    simp
  let s := ‖w‖
  let c : E := s⁻¹ • w
  have hc : ‖c‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hw
  have hac : inner ℝ a c = 0 := by simp [c, inner_smul_right, haw]
  have hca : inner ℝ c a = 0 := by rw [real_inner_comm, hac]
  let f : Fin 3 → E := ![a, c, 0]
  have hon : Orthonormal ℝ (({0, 1} : Set (Fin 3)).domRestrict f) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.domRestrict, f, ha, hc, hac, hca]
  obtain ⟨e, he⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := E) (ι := Fin 3) (v := f) (s := {0, 1})
    (by simpa only [Fintype.card_fin] using hdim) hon
  have he0 : e 0 = a := by simpa [f] using he 0 (by simp)
  have he1 : e 1 = c := by simpa [f] using he 1 (by simp)
  have huw : u = r • e 0 := by rw [he0]; exact hus
  have hws : w = s • e 1 := by
    rw [he1]
    simp [c, s, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hvw : v = beta • e 0 + s • e 1 := by rw [he0, ← hws]; exact hv
  have hscale (A : Four)
      (hfirst : ∀ a b c d, A ![a, b, c, d] = -A ![b, a, c, d])
      (hlast : ∀ a b c d, A ![a, b, c, d] = -A ![a, b, d, c]) :
      A ![u, v, u, v] = r ^ 2 * s ^ 2 * A ![e 0, e 1, e 0, e 1] := by
    rw [congrArg₂ (fun p q ↦ A ![p, q, p, q]) huw hvw]
    exact sectional_scale A hfirst hlast (e 0) (e 1) r s beta
  have hpos : 0 < r ^ 2 * s ^ 2 := mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr hu)) (sq_pos_of_pos (norm_pos_iff.mpr hw))
  have hsnull : S ![e 0, e 1, e 0, e 1] = 0 :=
    (mul_eq_zero.mp ((hscale S hSfirst hSlast).symm.trans hnull)).resolve_left (ne_of_gt hpos)
  rw [hscale W hWfirst hWlast]
  exact mul_nonneg (le_of_lt hpos) (hframe e hsnull)

private noncomputable def variationFour (B : Bilin) : Four :=
  (-2 : ℝ) • (gramFour B (innerₗ E) + gramFour (innerₗ E) B)

private theorem variationFour_first (B : Bilin) (a b c d : E) :
    variationFour B ![a, b, c, d] = -variationFour B ![b, a, c, d] := by
  simp only [variationFour, smul_apply]
  rw [gramFour_sum_first]
  ring

private theorem variationFour_last (B : Bilin) (a b c d : E) :
    variationFour B ![a, b, c, d] = -variationFour B ![a, b, d, c] := by
  simp only [variationFour, smul_apply, add_apply]
  rw [gramFour_last B (innerₗ E) a b c d, gramFour_last (innerₗ E) B a b c d]
  ring

private theorem variationFour_diag (B : Bilin)
    (hsymm : ∀ a b, B a b = B b a) (a b : E) :
    variationFour B ![a, b, a, b] =
      -2 * B a a * inner ℝ b b - 2 * inner ℝ a a * B b b +
        4 * B a b * inner ℝ a b := by
  simp only [variationFour, smul_apply, add_apply, gramFour_apply]
  change -2 * (B a a * inner ℝ b b - B a b * inner ℝ b a +
    (inner ℝ a a * B b b - inner ℝ a b * B b a)) = _
  rw [hsymm b a, real_inner_comm b a]
  ring

private noncomputable def shiftedSlice (T : Four) (epsilon : ℝ) (p : E) : Bilin :=
  inputSlice T p p + epsilon • (innerₗ E -
    LinearMap.BilinForm.linMulLin ((innerₗ E) p) ((innerₗ E) p))

private theorem shiftedSlice_apply (T : Four) (epsilon : ℝ) (p a c : E) :
    shiftedSlice T epsilon p a c = T ![a, p, c, p] + epsilon *
      (inner ℝ a c - inner ℝ p a * inner ℝ p c) := by
  simp only [shiftedSlice, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.BilinForm.linMulLin_apply, inputSlice_apply]
  rfl

private theorem shiftedSlice_symm (T : Four) (epsilon : ℝ) (p : E)
    (hpair : ∀ a b c d, T ![a, b, c, d] = T ![c, d, a, b]) :
    (shiftedSlice T epsilon p).IsSymm := by
  refine ⟨fun a c ↦ ?_⟩
  rw [shiftedSlice_apply, shiftedSlice_apply, hpair a p c p, real_inner_comm a c]
  ring

private theorem shiftedSlice_pos (T : Four) (epsilon : ℝ) (p : E)
    (hshift : ∀ a b, 0 ≤ T ![a, b, a, b] + epsilon *
      (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2))
    (hp : inner ℝ p p = 1) (a : E) : 0 ≤ shiftedSlice T epsilon p a a := by
  rw [shiftedSlice_apply]
  have h := hshift a p
  rw [hp, mul_one, real_inner_comm p a, pow_two] at h
  exact h

private theorem shiftedSlice_kernel (T : Four) (epsilon : ℝ) (p q : E)
    (hpair : ∀ a b c d, T ![a, b, c, d] = T ![c, d, a, b])
    (hshift : ∀ a b, 0 ≤ T ![a, b, a, b] + epsilon *
      (inner ℝ a a * inner ℝ b b - (inner ℝ a b) ^ 2))
    (hp : inner ℝ p p = 1) (hq : inner ℝ q q = 1) (hpq : inner ℝ p q = 0)
    (hnull : T ![q, p, q, p] = -epsilon) (z : E) :
    T ![q, p, z, p] = -epsilon * inner ℝ q z := by
  let C := shiftedSlice T epsilon p
  have hCnull : C q q = 0 := by
    rw [shiftedSlice_apply, hnull, hq, hpq]
    ring
  have hk : C q = 0 := LinearMap.mem_ker.mp
    ((C.apply_apply_same_eq_zero_iff (shiftedSlice_pos T epsilon p hshift hp)
      (LinearMap.BilinForm.isSymm_iff.mp (shiftedSlice_symm T epsilon p hpair))).mp hCnull)
  have h := congrArg (fun L : E →ₗ[ℝ] ℝ ↦ L z) hk
  change shiftedSlice T epsilon p q z = 0 at h
  rw [shiftedSlice_apply, hpq, zero_mul, sub_zero] at h
  linarith only [h]

private theorem curvatureBFour_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E) (e : OrthonormalBasis κ ℝ E) (T : Four)
    (a c d f : E) : curvatureBFour b T ![a, c, d, f] =
      curvatureBFour e T ![a, c, d, f] := by
  rw [curvatureBFour_apply, curvatureBFour_apply]
  simpa only [traceSlice_apply] using
    bilinear_contraction (traceSlice T a c) (traceSlice T d f) b e

set_option maxHeartbeats 800000 in

private theorem sectional_frame_identity
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (epsilon : ℝ)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hpair : ∀ a b c d, R a b c d = R c d a b)
    (hnull : R 0 1 0 1 = -epsilon) (h0102 : R 0 1 0 2 = 0)
    (h0112 : R 0 1 1 2 = 0) :
    2 * ((∑ i, ∑ j, R 0 i 1 j * R 0 i 1 j) -
      (∑ i, ∑ j, R 0 i 1 j * R 1 i 0 j) -
      (∑ i, ∑ j, R 0 i 1 j * R 1 i 0 j) +
      (∑ i, ∑ j, R 0 i 0 j * R 1 i 1 j)) +
      epsilon * ((∑ i, ∑ j, R i j i j) + 2 * epsilon) =
      2 * ((R 0 2 0 2 + epsilon) * (R 1 2 1 2 + epsilon) - (R 0 2 1 2) ^ 2) := by
  have hf (i k l) : R i i k l = 0 := by linarith only [hfirst i i k l]
  have hl (i j k) : R i j k k = 0 := by linarith only [hlast i j k k]
  have hrev (i j) : R j i j i = R i j i j := by
    rw [hfirst j i j i, hlast i j j i, neg_neg]
  have h0110 : R 0 1 1 0 = -R 0 1 0 1 := hlast 0 1 1 0
  have h0210 : R 0 2 1 0 = 0 := by
    rw [hlast 0 2 1 0, hpair 0 2 0 1, h0102, neg_zero]
  have h1202 : R 1 2 0 2 = R 0 2 1 2 := hpair 1 2 0 2
  norm_num [Fin.sum_univ_succ, hf, hl, h0110, h0112, h0210, h1202,
    hrev 0 1, hrev 0 2, hrev 1 2, hnull]
  ring

set_option maxHeartbeats 1000000 in

private theorem shifted_reaction_frame {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (T : Four) (B : Bilin)
    (e : OrthonormalBasis (Fin 3) ℝ E)
    (hfirst : ∀ a c d f, T ![a, c, d, f] = -T ![c, a, d, f])
    (hlast : ∀ a c d f, T ![a, c, d, f] = -T ![a, c, f, d])
    (hpair : ∀ a c d f, T ![a, c, d, f] = T ![d, f, a, c])
    (htrace : ∀ a c, B a c = ∑ i, T ![a, b i, c, b i])
    (epsilon : ℝ) (hshift : ∀ a c, 0 ≤ T ![a, c, a, c] + epsilon *
      (inner ℝ a a * inner ℝ c c - (inner ℝ a c) ^ 2))
    (hnull : T ![e 0, e 1, e 0, e 1] = -epsilon) :
    0 ≤ reactionFour b T B ![e 0, e 1, e 0, e 1] +
      epsilon * variationFour B ![e 0, e 1, e 0, e 1] +
      epsilon * ((∑ i, B (b i) (b i)) + 2 * epsilon) := by
  classical
  have hunit (i : Fin 3) : inner ℝ (e i) (e i) = 1 := by simp
  have h1 (z : E) : T ![e 0, e 1, z, e 1] = -epsilon * inner ℝ (e 0) z :=
    shiftedSlice_kernel T epsilon (e 1) (e 0) hpair hshift (hunit 1) (hunit 0)
      (by simp [e.inner_eq_ite]) hnull z
  have hnull' : T ![e 1, e 0, e 1, e 0] = -epsilon := by
    rw [hfirst (e 1) (e 0) (e 1) (e 0), hlast (e 0) (e 1) (e 1) (e 0),
      neg_neg, hnull]
  have h0 (z : E) : T ![e 0, e 1, e 0, z] = -epsilon * inner ℝ (e 1) z := by
    rw [hfirst (e 0) (e 1) (e 0) z, hlast (e 1) (e 0) (e 0) z, neg_neg]
    exact shiftedSlice_kernel T epsilon (e 0) (e 1) hpair hshift (hunit 0) (hunit 1)
      (by simp [e.inner_eq_ite]) hnull' z
  have h0102 : T ![e 0, e 1, e 0, e 2] = 0 := by
    simpa [e.inner_eq_ite] using h0 (e 2)
  have h0112 : T ![e 0, e 1, e 1, e 2] = 0 := by
    rw [hlast (e 0) (e 1) (e 1) (e 2), h1]
    simp [e.inner_eq_ite]
  have htrace_e (a c : E) : B a c = ∑ i, T ![a, e i, c, e i] := by
    rw [htrace]
    simpa only [traceSlice_apply] using bilinear_trace (traceSlice T a c) b e
  have hscalar : (∑ i, B (b i) (b i)) = ∑ i, ∑ j, T ![e i, e j, e i, e j] := by
    rw [bilinear_trace B b e]
    exact Finset.sum_congr rfl fun i hi ↦ htrace_e (e i) (e i)
  have hvar : variationFour B ![e 0, e 1, e 0, e 1] =
      -2 * (B (e 0) (e 0) + B (e 1) (e 1)) := by
    simp only [variationFour, smul_apply, add_apply, gramFour_apply]
    change -2 * (B (e 0) (e 0) * inner ℝ (e 1) (e 1) -
      B (e 0) (e 1) * inner ℝ (e 1) (e 0) +
      (inner ℝ (e 0) (e 0) * B (e 1) (e 1) -
        inner ℝ (e 0) (e 1) * B (e 1) (e 0))) = _
    simp [e.inner_eq_ite]
  have hframe := sectional_frame_identity
    (fun i j k l ↦ T ![e i, e j, e k, e l]) epsilon
    (fun i j k l ↦ hfirst (e i) (e j) (e k) (e l))
    (fun i j k l ↦ hlast (e i) (e j) (e k) (e l))
    (fun i j k l ↦ hpair (e i) (e j) (e k) (e l)) hnull h0102 h0112
  have hcs := (shiftedSlice T epsilon (e 2)).apply_sq_le_of_symm
    (shiftedSlice_pos T epsilon (e 2) hshift (hunit 2))
    (LinearMap.BilinForm.isSymm_iff.mp (shiftedSlice_symm T epsilon (e 2) hpair))
    (e 0) (e 1)
  simp only [shiftedSlice_apply] at hcs
  norm_num [e.inner_eq_ite, Fin.ext_iff] at hcs
  rw [reactionFour_apply, hpair (raiseBilin b B (e 0)) (e 1) (e 0) (e 1),
    hpair (e 0) (raiseBilin b B (e 1)) (e 0) (e 1)]
  simp only [h1, h0, raiseBilin_inner, hvar, hscalar,
    curvatureBFour_basis b e T, curvatureBFour_apply]
  have hcancel :
      2 * ((∑ i, ∑ j, T ![e 0, e i, e 1, e j] * T ![e 0, e i, e 1, e j]) -
        (∑ i, ∑ j, T ![e 0, e i, e 1, e j] * T ![e 1, e i, e 0, e j]) -
        (∑ i, ∑ j, T ![e 0, e i, e 1, e j] * T ![e 1, e i, e 0, e j]) +
        (∑ i, ∑ j, T ![e 0, e i, e 0, e j] * T ![e 1, e i, e 1, e j])) +
        epsilon * ((∑ i, ∑ j, T ![e i, e j, e i, e j]) + 2 * epsilon) ≥ 0 := by
    rw [hframe]
    linarith only [hcs]
  nlinarith only [hcancel]

set_option maxHeartbeats 1000000 in

private theorem shifted_sectional_reaction_bound [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (T : Four) (B : Bilin)
    (hdim : Module.finrank ℝ E = 3)
    (hfirst : ∀ a c d f, T ![a, c, d, f] = -T ![c, a, d, f])
    (hlast : ∀ a c d f, T ![a, c, d, f] = -T ![a, c, f, d])
    (hpair : ∀ a c d f, T ![a, c, d, f] = T ![d, f, a, c])
    (htrace : ∀ a c, B a c = ∑ i, T ![a, b i, c, b i])
    (epsilon : ℝ) (hshift : ∀ a c, 0 ≤ T ![a, c, a, c] + epsilon *
      (inner ℝ a a * inner ℝ c c - (inner ℝ a c) ^ 2))
    (u v : E) (hnull : T ![u, v, u, v] + epsilon *
      (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) = 0) :
    -epsilon * ((∑ i, B (b i) (b i)) + 2 * epsilon) *
      (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) ≤
      reactionFour b T B ![u, v, u, v] + epsilon * variationFour B ![u, v, u, v] := by
  let G := gramFour (innerₗ E) (innerₗ E)
  let S := T + epsilon • G
  let W := reactionFour b T B + epsilon • variationFour B +
    (epsilon * ((∑ i, B (b i) (b i)) + 2 * epsilon)) • G
  have hSfirst (a c d f : E) : S ![a, c, d, f] = -S ![c, a, d, f] := by
    simp only [S, add_apply, smul_apply]
    rw [hfirst a c d f, gramFour_first (innerₗ E) a c d f]
    ring
  have hSlast (a c d f : E) : S ![a, c, d, f] = -S ![a, c, f, d] := by
    simp only [S, add_apply, smul_apply]
    rw [hlast a c d f, gramFour_last (innerₗ E) (innerₗ E) a c d f]
    ring
  have hWfirst (a c d f : E) : W ![a, c, d, f] = -W ![c, a, d, f] := by
    simp only [W, add_apply, smul_apply]
    rw [reactionFour_first b T B hfirst hpair a c d f,
      variationFour_first B a c d f, gramFour_first (innerₗ E) a c d f]
    ring
  have hWlast (a c d f : E) : W ![a, c, d, f] = -W ![a, c, f, d] := by
    simp only [W, add_apply, smul_apply]
    rw [reactionFour_last b T B hlast a c d f,
      variationFour_last B a c d f, gramFour_last (innerₗ E) (innerₗ E) a c d f]
    ring
  have hG (a c : E) : G ![a, c, a, c] =
      inner ℝ a a * inner ℝ c c - (inner ℝ a c) ^ 2 := by
    rw [gramFour_apply]
    change inner ℝ a a * inner ℝ c c - inner ℝ a c * inner ℝ c a = _
    rw [real_inner_comm c a, pow_two]
  have hsnull : S ![u, v, u, v] = 0 := by
    simpa only [S, add_apply, smul_apply, smul_eq_mul, hG] using hnull
  have hn := sectional_nonneg_of_frame S W hdim hSfirst hSlast hWfirst hWlast
    (fun e hs ↦ by
      have hg : G ![e 0, e 1, e 0, e 1] = 1 := by rw [hG]; simp [e.inner_eq_ite]
      have he : T ![e 0, e 1, e 0, e 1] = -epsilon := by
        change T ![e 0, e 1, e 0, e 1] + epsilon * G ![e 0, e 1, e 0, e 1] = 0 at hs
        rw [hg, mul_one] at hs
        linarith only [hs]
      change 0 ≤ reactionFour b T B ![e 0, e 1, e 0, e 1] +
        epsilon * variationFour B ![e 0, e 1, e 0, e 1] +
        (epsilon * ((∑ i, B (b i) (b i)) + 2 * epsilon)) * G ![e 0, e 1, e 0, e 1]
      rw [hg, mul_one]
      exact shifted_reaction_frame b T B e hfirst hlast hpair htrace epsilon hshift he)
    u v hsnull
  change 0 ≤ reactionFour b T B ![u, v, u, v] + epsilon * variationFour B ![u, v, u, v] +
    (epsilon * ((∑ i, B (b i) (b i)) + 2 * epsilon)) * G ![u, v, u, v] at hn
  rw [hG] at hn
  linarith only [hn]

end Algebra

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem curvatureReaction_lower_bound_of_shiftedSectional_null
    (D : LeviCivitaData g) (x : M) (epsilon : ℝ)
    (hshift : ∀ a b : TangentSpace (𝓡 3) x,
      0 ≤ D.curvatureTensor x a b a b + epsilon *
        (g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2))
    (u v : TangentSpace (𝓡 3) x)
    (hnull : D.curvatureTensor x u v u v + epsilon *
      (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) = 0) :
    -epsilon * (D.scalarCurvature x + 2 * epsilon) *
      (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) ≤
      D.curvatureReaction x u v u v + epsilon *
        (-2 * D.ricci x u u * g.inner x v v - 2 * g.inner x u u * D.ricci x v v +
          4 * D.ricci x u v * g.inner x u v) := by
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
  have hK (a c d f : E) : curvatureBFour b T ![a, c, d, f] = D.curvatureB x a c d f := by
    rw [curvatureBFour_apply]
    change (∑ i, ∑ j, T ![a, b i, c, b j] * T ![d, b i, f, b j]) =
      ∑ i, ∑ j, D.curvatureTensor x a (b i) c (b j) * D.curvatureTensor x d (b i) f (b j)
    simp only [hR]
  have hQ : reactionFour b T B ![u, v, u, v] = D.curvatureReaction x u v u v := by
    rw [reactionFour_apply, raised_corrections]
    change 2 * (curvatureBFour b T ![u, v, u, v] - curvatureBFour b T ![u, v, v, u] -
      curvatureBFour b T ![u, v, v, u] + curvatureBFour b T ![u, u, v, v]) -
      (∑ i, (B u (b i) * T ![b i, v, u, v] + B v (b i) * T ![u, b i, u, v] +
        B u (b i) * T ![u, v, b i, v] + B v (b i) * T ![u, v, u, b i])) =
      2 * (D.curvatureB x u v u v - D.curvatureB x u v v u - D.curvatureB x u v v u +
        D.curvatureB x u u v v) -
        ∑ i, (D.ricci x u (b i) * D.curvatureTensor x (b i) v u v +
          D.ricci x v (b i) * D.curvatureTensor x u (b i) u v +
          D.ricci x u (b i) * D.curvatureTensor x u v (b i) v +
          D.ricci x v (b i) * D.curvatureTensor x u v u (b i))
    apply congrArg₂ (fun a c : ℝ ↦ 2 * a - c)
    · simp only [hK]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hB u (b i), hB v (b i), hR (b i) v u v, hR u (b i) u v,
        hR u v (b i) v, hR u v u (b i)]
  have hV : variationFour B ![u, v, u, v] =
      -2 * D.ricci x u u * g.inner x v v - 2 * g.inner x u u * D.ricci x v v +
        4 * D.ricci x u v * g.inner x u v := by
    rw [variationFour_diag B hsymm]
    simp only [hB, hinner]
  have hscalar : (∑ i, B (b i) (b i)) = D.scalarCurvature x := by
    simp only [hB]
    rfl
  have h := shifted_sectional_reaction_bound b T B hdim hfirst hlast hpair htrace epsilon
    (fun a c ↦ by rw [hR, hinner, hinner, hinner]; exact hshift a c) u v
    (by rw [hR, hinner, hinner, hinner]; exact hnull)
  calc
    _ = -epsilon * ((∑ i, B (b i) (b i)) + 2 * epsilon) *
        (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2) := by
      rw [hscalar, hinner u u, hinner v v, hinner u v]
    _ ≤ reactionFour b T B ![u, v, u, v] + epsilon * variationFour B ![u, v, u, v] := h
    _ = _ := by rw [hQ, hV]

theorem curvatureReaction_nonneg_of_nonnegativeSectionalAt_null
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ a b : TangentSpace (𝓡 3) x, 0 ≤ D.curvatureTensor x a b a b)
    (u v : TangentSpace (𝓡 3) x) (hnull : D.curvatureTensor x u v u v = 0) :
    0 ≤ D.curvatureReaction x u v u v := by
  simpa only [neg_zero, zero_mul, add_zero] using
    curvatureReaction_lower_bound_of_shiftedSectional_null D x 0
      (fun a b ↦ by simpa only [zero_mul, add_zero] using hsec a b) u v
      (by simpa only [zero_mul, add_zero] using hnull)

end PoincareConjecture.M04


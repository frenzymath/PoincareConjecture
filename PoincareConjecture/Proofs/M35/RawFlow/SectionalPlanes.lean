import PoincareConjecture.Proofs.M04.SectionalMinimumDiffusion
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open M04

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem sectional_four_scale
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hfirst : ∀ a b c d, A ![a, b, c, d] = -A ![b, a, c, d])
    (hlast : ∀ a b c d, A ![a, b, c, d] = -A ![a, b, d, c])
    (p q : E) (r d s : ℝ) :
    A ![r • p, d • p + s • q, r • p, d • p + s • q] =
      r ^ 2 * s ^ 2 * A ![p, q, p, q] := by
  have hs0 (a b c f : E) (z : ℝ) :
      A ![z • a, b, c, f] = z * A ![a, b, c, f] := by
    simpa only [Matrix.vecCons, smul_eq_mul] using A.cons_smul ![b, c, f] z a
  have hs1 (a b c f : E) (z : ℝ) :
      A ![a, z • b, c, f] = z * A ![a, b, c, f] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons, smul_eq_mul] using
      (A.curryLeft a).cons_smul ![c, f] z b
  have hs2 (a b c f : E) (z : ℝ) :
      A ![a, b, z • c, f] = z * A ![a, b, c, f] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons, smul_eq_mul] using
      ((A.curryLeft a).curryLeft b).cons_smul ![f] z c
  have hs3 (a b c f : E) (z : ℝ) :
      A ![a, b, c, z • f] = z * A ![a, b, c, f] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons, smul_eq_mul] using
      (((A.curryLeft a).curryLeft b).curryLeft c).cons_smul ![] z f
  have ha1 (a b c f z : E) :
      A ![a, b + c, f, z] = A ![a, b, f, z] + A ![a, c, f, z] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
      (A.curryLeft a).cons_add ![f, z] b c
  have ha3 (a b c f z : E) :
      A ![a, b, c, f + z] = A ![a, b, c, f] + A ![a, b, c, z] := by
    simpa only [MultilinearMap.curryLeft_apply, Matrix.vecCons] using
      (((A.curryLeft a).curryLeft b).curryLeft c).cons_add ![] f z
  have hf (a b c : E) : A ![a, a, b, c] = 0 := by linarith only [hfirst a a b c]
  have hl (a b c : E) : A ![a, b, c, c] = 0 := by linarith only [hlast a b c c]
  simp only [hs0, hs2, ha1, ha3, hs1, hs3, hf, hl]
  ring

private theorem sectional_four_nonneg_of_orthonormal
    (A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hfirst : ∀ a b c d, A ![a, b, c, d] = -A ![b, a, c, d])
    (hlast : ∀ a b c d, A ![a, b, c, d] = -A ![a, b, d, c])
    (hunit : ∀ p q : E, ‖p‖ = 1 → ‖q‖ = 1 → inner ℝ p q = 0 →
      0 ≤ A ![p, q, p, q]) (u v : E) : 0 ≤ A ![u, v, u, v] := by
  by_cases hu : u = 0
  · subst u
    rw [A.map_coord_zero (0 : Fin 4) rfl]
  let r := ‖u‖
  let p := r⁻¹ • u
  have hp : ‖p‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
  have hup : u = r • p := by
    simp [p, r, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu)]
  let d := inner ℝ p v
  let w := v - d • p
  have hvw : v = d • p + w := by dsimp only [w]; abel
  have hpw : inner ℝ p w = 0 := by simp [w, d, inner_sub_right, inner_smul_right, hp]
  by_cases hw : w = 0
  · have hv0 : v = d • p + (0 : ℝ) • (0 : E) := by simpa [hw] using hvw
    rw [congrArg₂ (fun a b => A ![a, b, a, b]) hup hv0,
      sectional_four_scale A hfirst hlast p 0 r d 0]
    simp
  let s := ‖w‖
  let q := s⁻¹ • w
  have hq : ‖q‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hw
  have hpq : inner ℝ p q = 0 := by simp [q, inner_smul_right, hpw]
  have hwq : w = s • q := by
    simp [q, s, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hvq : v = d • p + s • q := by rw [← hwq]; exact hvw
  rw [congrArg₂ (fun a b => A ![a, b, a, b]) hup hvq,
    sectional_four_scale A hfirst hlast p q r d s]
  exact mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg s)) (hunit p q hp hq hpq)

end Algebra

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)

theorem modelPair_linearIndependent {p : V × V} (hp : p ∈ modelOrthonormalPairs n) :
    LinearIndependent ℝ ![p.1, p.2] := by
  apply Orthonormal.linearIndependent
  constructor
  · intro i
    fin_cases i
    · exact hp.1
    · exact hp.2.1
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hp.2.2
    · change inner ℝ p.2 p.1 = 0
      rw [real_inner_comm]
      exact hp.2.2
    · exact (hij rfl).elim

theorem metricGram_pos_of_modelPair (g : RiemannianMetric n V) (x : V)
    {p : V × V} (hp : p ∈ modelOrthonormalPairs n) : 0 < metricGram g x p.1 p.2 :=
  metricGram_pos_of_linearIndependent g x p.1 p.2 (modelPair_linearIndependent hp)



theorem sectional_lower_of_modelPairs {g : RiemannianMetric n V} (D : LeviCivitaData g)
    (x : V) (m : ℝ)
    (hmin : ∀ p ∈ modelOrthonormalPairs n, m ≤ D.sectionalCurvature x p.1 p.2)
    (u v : V) : m * metricGram g x u v ≤ D.curvatureTensor x u v u v := by
  obtain ⟨R, hR⟩ := (isSmoothCovariantTensor_riemannEvaluation D).1 x
  obtain ⟨G, hG⟩ := (isSmoothCovariantTensor_metricGramEvaluation g).1 x
  let e := trivializationAt V (TangentSpace (𝓡 n)) x
  let f := e.symmL ℝ x
  have hf (v : V) : f v = v := by
    simp only [f, e, TangentBundle.symmL_model_space]
    rfl
  let A : MultilinearMap ℝ (fun _ : Fin 4 => V) ℝ :=
    (R - m • G).compLinearMap (fun _ => f.toLinearMap)
  have hA (a b c d : V) : A ![a, b, c, d] = D.curvatureTensor x a b c d -
      m * (g.inner x a c * g.inner x b d - g.inner x a d * g.inner x b c) := by
    simp only [A, MultilinearMap.compLinearMap_apply, ContinuousLinearMap.coe_coe,
      sub_apply, smul_apply, smul_eq_mul, ← hR, ← hG,
      LeviCivitaData.riemannEvaluation, metricGramEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hf]
  have hfirst (a b c d : V) : A ![a, b, c, d] = -A ![b, a, c, d] := by
    rw [hA, hA, curvatureTensor_swap_first D]
    ring
  have hlast (a b c d : V) : A ![a, b, c, d] = -A ![a, b, d, c] := by
    rw [hA, hA, curvatureTensor_swap_last D]
    ring
  have hdiag (a b : V) : A ![a, b, a, b] =
      D.curvatureTensor x a b a b - m * metricGram g x a b := by
    rw [hA, g.symm x b a]
    simp only [metricGram, pow_two]
  have hunit (p q : V) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : inner ℝ p q = 0) :
      0 ≤ A ![p, q, p, q] := by
    rw [hdiag]
    have hpq' : (p, q) ∈ modelOrthonormalPairs n := ⟨hp, hq, hpq⟩
    have hpos := metricGram_pos_of_modelPair g x hpq'
    exact sub_nonneg.mpr ((le_div_iff₀ hpos).mp (hmin (p, q) hpq'))
  have h := sectional_four_nonneg_of_orthonormal A hfirst hlast hunit u v
  rw [hdiag] at h
  exact sub_nonneg.mp h

end PoincareConjecture.M35.Uniqueness

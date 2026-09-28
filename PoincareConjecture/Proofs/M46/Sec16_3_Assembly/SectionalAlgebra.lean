import PoincareConjecture.Proofs.M04.CompactSectionalPreservation
import PoincareConjecture.Definitions.Ch04.Pinching









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.M04

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem alternating_pair_scale
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
  have hf (a b c : E) : A ![a, a, b, c] = 0 := by
    linarith only [hfirst a a b c]
  have hl (a b c : E) : A ![a, b, c, c] = 0 := by
    linarith only [hlast a b c c]
  simp only [hs0, hs2, ha1, ha3, hs1, hs3, hf, hl]
  ring

private theorem alternating_pair_nonnegative
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
      alternating_pair_scale A hfirst hlast p 0 r d 0]
    simp
  let s := ‖w‖
  let q := s⁻¹ • w
  have hq : ‖q‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hw
  have hpq : inner ℝ p q = 0 := by simp [q, inner_smul_right, hpw]
  have hwq : w = s • q := by
    simp [q, s, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hvq : v = d • p + s • q := by rw [← hwq]; exact hvw
  rw [congrArg₂ (fun a b => A ![a, b, a, b]) hup hvq,
    alternating_pair_scale A hfirst hlast p q r d s]
  exact mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg s)) (hunit p q hp hq hpq)

end Algebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in


theorem sectional_lower_from_model_pairs (D : LeviCivitaData g) (c y : M)
    (hy : y ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) c).baseSet) (m : ℝ)
    (hmin : ∀ p ∈ modelOrthonormalPairs n,
      let e := trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) c
      m * metricGram g y (e.symmL ℝ y p.1) (e.symmL ℝ y p.2) ≤
        D.curvatureTensor y (e.symmL ℝ y p.1) (e.symmL ℝ y p.2)
          (e.symmL ℝ y p.1) (e.symmL ℝ y p.2))
    (u v : TangentSpace (𝓡 n) y) : m * metricGram g y u v ≤ D.curvatureTensor y u v u v := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := trivializationAt E (TangentSpace (𝓡 n) : M → Type _) c
  let f := e.symmL ℝ y
  obtain ⟨R, hR⟩ := (isSmoothCovariantTensor_riemannEvaluation D).1 y
  obtain ⟨G, hG⟩ := (isSmoothCovariantTensor_metricGramEvaluation g).1 y
  let A : MultilinearMap ℝ (fun _ : Fin 4 => E) ℝ :=
    (R - m • G).compLinearMap (fun _ => f.toLinearMap)
  have hA (a b c d : E) : A ![a, b, c, d] =
      D.curvatureTensor y (f a) (f b) (f c) (f d) -
        m * (g.inner y (f a) (f c) * g.inner y (f b) (f d) -
          g.inner y (f a) (f d) * g.inner y (f b) (f c)) := by
    simp only [A, MultilinearMap.compLinearMap_apply, ContinuousLinearMap.coe_coe,
      sub_apply, smul_apply, smul_eq_mul, ← hR, ← hG,
      LeviCivitaData.riemannEvaluation, metricGramEvaluation,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hfirst (a b c d : E) : A ![a, b, c, d] = -A ![b, a, c, d] := by
    rw [hA, hA, curvatureTensor_swap_first D]
    ring
  have hlast (a b c d : E) : A ![a, b, c, d] = -A ![a, b, d, c] := by
    rw [hA, hA, curvatureTensor_swap_last D]
    ring
  have hdiag (a b : E) : A ![a, b, a, b] =
      D.curvatureTensor y (f a) (f b) (f a) (f b) - m * metricGram g y (f a) (f b) := by
    rw [hA, g.symm y (f b) (f a)]
    simp only [metricGram, pow_two]
  have hall (a b : E) : 0 ≤ A ![a, b, a, b] :=
    alternating_pair_nonnegative A hfirst hlast (fun p q hp hq hpq => by
      rw [hdiag]
      exact sub_nonneg.mpr (hmin (p, q) ⟨hp, hq, hpq⟩)) a b
  have h := hall (e.continuousLinearMapAt ℝ y u) (e.continuousLinearMapAt ℝ y v)
  rw [hdiag] at h
  simpa only [f, e.symmL_continuousLinearMapAt hy] using sub_nonneg.mp h

set_option backward.isDefEq.respectTransparency false in


theorem scalar_lower_of_sectional_lower {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    {g : RiemannianMetric 3 N} (D : LeviCivitaData g) (x : N) (m : ℝ)
    (hsec : ∀ u v : TangentSpace (𝓡 3) x,
      m * metricGram g x u v ≤ D.curvatureTensor x u v u v) :
    6 * m ≤ D.scalarCurvature x := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
    exact finrank_euclideanSpace_fin
  have hgram (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      metricGram g x (b i) (b j) = if i = j then 0 else 1 := by
    change inner ℝ (b i) (b i) * inner ℝ (b j) (b j) -
      (inner ℝ (b i) (b j)) ^ 2 = _
    simp only [b.inner_eq_one, b.inner_eq_ite]
    split_ifs <;> norm_num
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hsec (b i) (b j)))
  change (∑ i, ∑ j, m * metricGram g x (b i) (b j)) ≤ D.scalarCurvature x at h
  simp_rw [hgram, mul_ite, mul_zero, mul_one] at h
  have hrow (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x))) :
      (∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
        if i = j then 0 else m) = 2 * m := by
    calc
      _ = ∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) x)),
          (m - if i = j then m else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = 3 * m - m := by simp [Finset.sum_sub_distrib, hdim]
      _ = 2 * m := by ring
  simp_rw [hrow] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    hdim, nsmul_eq_mul] at h
  norm_num at h
  linarith

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in


theorem curvature_pair_positive_of_orthonormal {N : Type u} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    {g : RiemannianMetric 3 N} (D : LeviCivitaData g) (x : N)
    (hpos : ∀ a b : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x a b → 0 < D.sectionalCurvature x a b)
    (u v : TangentSpace (𝓡 3) x) (hlin : LinearIndependent ℝ ![u, v]) :
    0 < D.curvatureTensor x u v u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let E := TangentSpace (𝓡 3) x
  have hgram : 0 < inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2 :=
    metricGram_pos_of_linearIndependent g x u v hlin
  have hu : u ≠ 0 := by
    intro hu
    simp [hu] at hgram
  let r := ‖u‖
  let p : E := r⁻¹ • u
  have hp : ‖p‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
  have hpp : inner ℝ p p = 1 := by rw [real_inner_self_eq_norm_sq, hp]; norm_num
  have hup : u = r • p := by
    simp [p, r, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu)]
  let d := inner ℝ p v
  let w := v - d • p
  have hvw : v = d • p + w := by dsimp only [w]; abel
  have hpw : inner ℝ p w = 0 := by simp [w, d, inner_sub_right, inner_smul_right, hp]
  have hw : w ≠ 0 := by
    intro hw0
    have hv : v = d • p := by simpa [hw0] using hvw
    rw [hup, hv] at hgram
    simp only [inner_smul_left, inner_smul_right, conj_trivial, hpp, mul_one] at hgram
    nlinarith
  let s := ‖w‖
  let q : E := s⁻¹ • w
  have hq : ‖q‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hw
  have hqq : inner ℝ q q = 1 := by rw [real_inner_self_eq_norm_sq, hq]; norm_num
  have hpq : inner ℝ p q = 0 := by simp [q, inner_smul_right, hpw]
  have hwq : w = s • q := by
    simp [q, s, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hvq : v = d • p + s • q := by rw [← hwq]; exact hvw
  have hpair : LeviCivitaData.IsOrthonormalPair g x p q := ⟨hpp, hqq, hpq⟩
  have hpqpos : 0 < D.curvatureTensor x p q p q := by
    have h := hpos p q hpair
    simpa only [LeviCivitaData.sectionalCurvature, hpair.1, hpair.2.1, hpair.2.2,
      one_mul, zero_pow (by decide : 2 ≠ 0), sub_zero, div_one] using h
  obtain ⟨A, hA⟩ := (isSmoothCovariantTensor_riemannEvaluation D).1 x
  have hR (a b c d : E) : D.curvatureTensor x a b c d = A ![a, b, c, d] := hA ![a, b, c, d]
  have hfirst (a b c d : E) : A ![a, b, c, d] = -A ![b, a, c, d] := by
    simpa only [← hR] using curvatureTensor_swap_first D x b a c d
  have hlast (a b c d : E) : A ![a, b, c, d] = -A ![a, b, d, c] := by
    simpa only [← hR] using curvatureTensor_swap_last D x a b c d
  rw [hR, congrArg₂ (fun a b => A ![a, b, a, b]) hup hvq,
    alternating_pair_scale A hfirst hlast p q r d s, ← hR]
  exact mul_pos (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hu))
    (sq_pos_of_pos (norm_pos_iff.mpr hw))) hpqpos

end PoincareConjecture.Proofs.M46

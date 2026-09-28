import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.CompactDirections
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.Sectional.Rayleigh
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Calculus.Identities.CurvatureSymmetries
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.Sectional.MinimumDiffusion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Positivity.Sectional.NullReaction
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Maximum.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.Homeomorph.Lemmas












set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology

universe u

namespace PoincareConjecture.RicciFlowAnalysis

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem sectional_four_scale
    (A : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)
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

private theorem sectional_four_nonneg_of_orthonormal
    (A : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ)
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
  have hpw : inner ℝ p w = 0 := by
    simp [w, d, inner_sub_right, inner_smul_right, hp]
  by_cases hw : w = 0
  · have hv0 : v = d • p + (0 : ℝ) • (0 : E) := by simpa [hw] using hvw
    rw [congrArg₂ (fun a b ↦ A ![a, b, a, b]) hup hv0,
      sectional_four_scale A hfirst hlast p 0 r d 0]
    simp
  let s := ‖w‖
  let q := s⁻¹ • w
  have hq : ‖q‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hw
  have hpq : inner ℝ p q = 0 := by simp [q, inner_smul_right, hpw]
  have hwq : w = s • q := by
    simp [q, s, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hvq : v = d • p + s • q := by rw [← hwq]; exact hvw
  rw [congrArg₂ (fun a b ↦ A ![a, b, a, b]) hup hvq,
    sectional_four_scale A hfirst hlast p q r d s]
  exact mul_nonneg (mul_nonneg (sq_nonneg r) (sq_nonneg s)) (hunit p q hp hq hpq)

end Algebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
private theorem sectional_lower_of_model_pairs (D : LeviCivitaData g) (c y : M)
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
  let A : MultilinearMap ℝ (fun _ : Fin 4 ↦ E) ℝ :=
    (R - m • G).compLinearMap (fun _ ↦ f.toLinearMap)
  have hA (a b c d : E) : A ![a, b, c, d] =
      D.curvatureTensor y (f a) (f b) (f c) (f d) -
        m * (g.inner y (f a) (f c) * g.inner y (f b) (f d) -
          g.inner y (f a) (f d) * g.inner y (f b) (f c)) := by
    simp only [A, MultilinearMap.compLinearMap_apply, ContinuousLinearMap.coe_coe,
      sub_apply, smul_apply,
      smul_eq_mul, ← hR, ← hG, LeviCivitaData.riemannEvaluation, metricGramEvaluation,
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
    sectional_four_nonneg_of_orthonormal A hfirst hlast
      (fun p q hp hq hpq ↦ by
        rw [hdiag]
        exact sub_nonneg.mpr (hmin (p, q) ⟨hp, hq, hpq⟩)) a b
  have h := hall (e.continuousLinearMapAt ℝ y u) (e.continuousLinearMapAt ℝ y v)
  rw [hdiag] at h
  simpa only [f, e.symmL_continuousLinearMapAt hy] using sub_nonneg.mp h


end PoincareConjecture.RicciFlowAnalysis

namespace PoincareConjecture.RicciFlowAnalysis

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

set_option maxHeartbeats 4800000 in

set_option backward.isDefEq.respectTransparency false in
theorem nonnegativeSectionalCurvature_preserved_compact
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {T : ℝ} (hT : 0 < T) (F : RicciFlow 3 M (Icc 0 T))
    (hinit : (F.connection 0).NonnegativeSectionalCurvature) :
    ∀ t ∈ Icc 0 T, (F.connection t).NonnegativeSectionalCurvature := by
  classical
  let E := EuclideanSpace ℝ (Fin 3)
  let e := fun c : M ↦ trivializationAt E (TangentSpace (𝓡 3) : M → Type _) c
  obtain ⟨s, K, hK, hKe, hcover⟩ := exists_finite_compact_tangent_cover (n := 3) (M := M)
  let P := modelOrthonormalPairs 3
  let C := (i : s) × (K i.1) × P
  let (c : M) : CompactSpace (K c) := isCompact_iff_compactSpace.mp (hK c)
  let : CompactSpace P := isCompact_iff_compactSpace.mp (isCompact_modelOrthonormalPairs 3)
  let : CompactSpace C := inferInstance
  let X : C → M := fun z ↦ z.2.1.1
  let U : (z : C) → TangentSpace (𝓡 3) (X z) :=
    fun z ↦ (e z.1.1).symmL ℝ (X z) z.2.2.1.1
  let V : (z : C) → TangentSpace (𝓡 3) (X z) :=
    fun z ↦ (e z.1.1).symmL ℝ (X z) z.2.2.1.2
  have hlin (z : C) : LinearIndependent ℝ ![U z, V z] := by
    have hp := z.2.2.2
    have horth : Orthonormal ℝ (![z.2.2.1.1, z.2.2.1.2] : Fin 2 → E) := by
      constructor
      · intro i
        fin_cases i
        · exact hp.1
        · exact hp.2.1
      · intro i j hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hp.2.2
        · change inner ℝ z.2.2.1.2 z.2.2.1.1 = 0
          rw [real_inner_comm]
          exact hp.2.2
        · exact (hij rfl).elim
    have hy : X z ∈ (e z.1.1).baseSet := hKe z.1.1 z.2.1.2
    have hinj : Function.Injective ((e z.1.1).symmL ℝ (X z)) := by
      intro a b hab
      have h := congrArg ((e z.1.1).continuousLinearMapAt ℝ (X z)) hab
      simpa only [(e z.1.1).continuousLinearMapAt_symmL hy] using h
    have h := horth.linearIndependent.map' ((e z.1.1).symmL ℝ (X z)).toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
    convert! h using 1
    funext i
    fin_cases i <;> rfl
  let R : ℝ → C → ℝ := fun t z ↦ (F.connection t).curvatureTensor (X z) (U z) (V z) (U z) (V z)
  let G : ℝ → C → ℝ := fun t z ↦ metricGram (F.metric t) (X z) (U z) (V z)
  let q : ℝ → C → ℝ := fun t z ↦ R t z / G t z
  have hG (t : ℝ) (z : C) : 0 < G t z :=
    metricGram_pos_of_linearIndependent (F.metric t) (X z) (U z) (V z) (hlin z)
  have hX : Continuous X := by
    apply continuous_sigma
    intro i
    exact continuous_subtype_val.comp continuous_fst
  have hqc : Continuous (fun p : (Icc (0 : ℝ) T) × C ↦ q p.1 p.2) := by
    let D := (i : s) × ((K i.1) × P) × Icc (0 : ℝ) T
    let d : C × Icc (0 : ℝ) T ≃ₜ D := Homeomorph.sigmaProdDistrib
    have h : Continuous (fun z : D ↦ q z.2.2 ⟨z.1, z.2.1⟩) := by
      apply continuous_sigma
      intro i
      have hp : Continuous (fun p : ((K i.1) × P) × Icc (0 : ℝ) T ↦
          (((p.2 : ℝ), (p.1.1 : M)), (p.1.2 : E × E))) := by fun_prop
      exact (continuousOn_flow_sectionalRayleigh_trivialization F i.1).comp_continuous hp
        (fun p ↦ ⟨⟨p.2.2, hKe i.1 p.1.1.2⟩, p.1.2.2⟩)
    have hs : Continuous (fun p : C × Icc (0 : ℝ) T ↦ q p.2 p.1) :=
      h.comp d.continuous
    exact hs.comp continuous_swap
  have hq : ContinuousOn (Function.uncurry q) (Icc 0 T ×ˢ (univ : Set C)) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hmap : Continuous (fun p : Icc 0 T ×ˢ (univ : Set C) ↦
        ((⟨p.1.1, p.2.1⟩ : Icc (0 : ℝ) T), p.1.2)) := by fun_prop
    exact hqc.comp hmap
  have hcomplete (t m : ℝ) (h : ∀ z : C, m ≤ q t z) :
      ∀ (y : M) (a b : TangentSpace (𝓡 3) y),
        m * metricGram (F.metric t) y a b ≤ (F.connection t).curvatureTensor y a b a b := by
    intro y a b
    have hycover : y ∈ ⋃ c ∈ s, K c := hcover ▸ mem_univ y
    obtain ⟨c, hc, hyK⟩ := mem_iUnion₂.mp hycover
    apply sectional_lower_of_model_pairs (F.connection t) c y (hKe c hyK) m _ a b
    intro p hp
    let z : C := ⟨⟨c, hc⟩, ⟨⟨y, hyK⟩, ⟨p, hp⟩⟩⟩
    exact (le_div_iff₀ (hG t z)).mp (h z)
  have hscalar : Continuous (fun p : (Icc (0 : ℝ) T) × C ↦
      (F.connection p.1).scalarCurvature (X p.2)) :=
    F.contMDiffOn_scalarCurvature.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk (hX.comp continuous_snd))
      (fun p ↦ ⟨p.1.2, mem_univ (X p.2)⟩)
  obtain ⟨A, hA⟩ := isCompact_univ.bddAbove_image
    (hscalar.sub (continuous_const.mul hqc)).continuousOn
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) (z : C) :
      (F.connection t).scalarCurvature (X z) - 2 * q t z ≤ A :=
    hA ⟨(⟨t, ht⟩, z), mem_univ _, rfl⟩
  let L : ℝ → C → ℝ := fun t z ↦
    (F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
      (X z) ![U z, V z, U z, V z]
  let Q : ℝ → C → ℝ := fun t z ↦
    (F.connection t).curvatureReaction (X z) (U z) (V z) (U z) (V z)
  let H : ℝ → C → ℝ := fun t z ↦
    -2 * (F.connection t).ricci (X z) (U z) (U z) * (F.metric t).inner (X z) (V z) (V z) -
      2 * (F.metric t).inner (X z) (U z) (U z) * (F.connection t).ricci (X z) (V z) (V z) +
      4 * (F.connection t).ricci (X z) (U z) (V z) * (F.metric t).inner (X z) (U z) (V z)
  let velocity : ℝ → C → ℝ := fun t z ↦
    (L t z + Q t z) / G t z - R t z * H t z / (G t z) ^ 2
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) (z : C) :
      HasDerivWithinAt (fun s ↦ q s z) (velocity t z) (Icc 0 T) t :=
    hasDerivWithinAt_sectionalRayleigh F t ht (X z) (U z) (V z) (hG t z)
  have hminimum (t : ℝ) (ht : t ∈ Ioc 0 T) (z : C)
      (hspace : ∀ y : C, q t z ≤ q t y) (hnonpos : q t z ≤ 0) :
      -(-A) * q t z ≤ velocity t z := by
    let m := q t z
    have hlower := hcomplete t m hspace
    have hnull : (F.connection t).curvatureTensor (X z) (U z) (V z) (U z) (V z) =
        m * metricGram (F.metric t) (X z) (U z) (V z) :=
      (div_mul_cancel₀ (R t z) (hG t z).ne').symm
    have hlap : 0 ≤ L t z :=
      curvature_tensorLaplacian_nonneg_at_sectional_rayleigh_min (F.connection t)
        m hlower (X z) (U z) (V z) hnull
    have hshift : ∀ a b : TangentSpace (𝓡 3) (X z),
        0 ≤ (F.connection t).curvatureTensor (X z) a b a b +
          (-m) * metricGram (F.metric t) (X z) a b := by
      intro a b
      have h := hlower (X z) a b
      linarith
    have hzshift : (F.connection t).curvatureTensor (X z) (U z) (V z) (U z) (V z) +
        (-m) * metricGram (F.metric t) (X z) (U z) (V z) = 0 := by rw [hnull]; ring
    have hreact : m * ((F.connection t).scalarCurvature (X z) - 2 * m) * G t z ≤
        Q t z - m * H t z := by
      have h := curvatureReaction_lower_bound_of_shiftedSectional_null
        (F.connection t) (X z) (-m) hshift (U z) (V z) hzshift
      change -(-m) * ((F.connection t).scalarCurvature (X z) + 2 * (-m)) * G t z ≤
        Q t z + (-m) * H t z at h
      convert! h using 1 <;> ring
    have hvelocity : velocity t z * G t z = L t z + Q t z - m * H t z := by
      change ((L t z + Q t z) / G t z - R t z * H t z / (G t z) ^ 2) * G t z = _
      have hr : R t z = m * G t z := hnull
      rw [hr]
      field_simp [(hG t z).ne']
    have hreaction : m * ((F.connection t).scalarCurvature (X z) - 2 * m) ≤ velocity t z := by
      apply (mul_le_mul_iff_left₀ (hG t z)).mp
      nlinarith only [hreact, hlap, hvelocity]
    have hb := hbound t ⟨ht.1.le, ht.2⟩ z
    change (F.connection t).scalarCurvature (X z) - 2 * m ≤ A at hb
    change m ≤ 0 at hnonpos
    change -(-A) * m ≤ velocity t z
    simp only [neg_neg]
    nlinarith only [hreaction, hb, hnonpos]
  have hqinit (z : C) : 0 ≤ q 0 z := div_nonneg (hinit (X z) (U z) (V z)) (hG 0 z).le
  have hpres := compact_min_velocity_nonnegative (K := -A) hT q velocity hq hd hminimum hqinit
  intro t ht
  change ∀ (y : M) (a b : TangentSpace (𝓡 3) y),
    0 ≤ (F.connection t).curvatureTensor y a b a b
  simpa only [zero_mul] using hcomplete t 0 (hpres t ht)

end PoincareConjecture.RicciFlowAnalysis

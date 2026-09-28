import PoincareConjecture.Proofs.M63.Sec19_8_LocalEstimates.CurvatureJetSpatialCalculus
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m63TangentJetPair_arc_iterate [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (i j m : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    let K : ℕ → (y : ℝ) → TangentSpace (𝓡 n) (c y t) := fun k =>
      match k with
      | 0 => spatialUnitTangent F c t
      | k + 1 => m63CurvatureJet F c k t
    ((m62ArcDerivative F c t)^[m])
      (fun y => (F.metric t).inner (c y t) (K i y) (K j y)) x =
      ∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℝ) *
        (F.metric t).inner (c x t) (K (i + p.1) x) (K (j + p.2) x) := by
  let K : ℕ → (y : ℝ) → TangentSpace (𝓡 n) (c y t) := fun k =>
    match k with
    | 0 => spatialUnitTangent F c t
    | k + 1 => m63CurvatureJet F c k t
  let Y : ℕ → (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2) := fun k =>
    match k with
    | 0 => fun z => spatialUnitTangent F c z.2 z.1
    | k + 1 => fun z => m63CurvatureJet F c k z.2 z.1
  let P : ℕ → ℕ → ℝ → ℝ := fun r s y =>
    (F.metric t).inner (c y t) (K r y) (K s y)
  have hY (k : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n).tangent ∞
      (fun z => (⟨c z.1 z.2, Y k z⟩ : TangentBundle (𝓡 n) M))
      (univ ×ˢ Ioo a b) := by
    cases k with
    | zero => exact unitTangent_joint_contMDiff F c hc
    | succ k => exact M63.curvatureJet_joint_contMDiff F c hc k
  have hYK (r : ℕ) (y : ℝ) : Y r (y, t) = K r y := by
    cases r <;> rfl
  have hP (r s : ℕ) : ContDiff ℝ ∞ (P r s) := by
    have h := (metric_pairing_contDiffOn F c hc.joint_smooth
      (Y r) (Y s) (hY r) (hY s)).comp_contDiff
        (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
    simpa only [Function.comp_def, hYK, id_eq, P] using h
  have hnext (r : ℕ) (y : ℝ) :
      m62SpatialDerivative F c t (K r) y = K (r + 1) y := by
    cases r <;> rfl
  have hpair (r s : ℕ) (y : ℝ) :
      m62ArcDerivative F c t (P r s) y = P (r + 1) s y + P r (s + 1) y := by
    have h := m63ArcDerivative_metric_pairing F c hc (Y r) (Y s) (hY r) (hY s) ht y
    simp only [hYK] at h
    change m62ArcDerivative F c t (P r s) y =
      (F.metric t).inner (c y t) (m62SpatialDerivative F c t (K r) y) (K s y) +
        (F.metric t).inner (c y t) (K r y) (m62SpatialDerivative F c t (K s) y) at h
    simpa only [hnext] using h
  change ((m62ArcDerivative F c t)^[m]) (P i j) x =
    ∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℝ) * P (i + p.1) (j + p.2) x
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rw [show ((m62ArcDerivative F c t)^[m]) (P i j) =
      (fun y => ∑ p ∈ Finset.antidiagonal m,
        (m.choose p.1 : ℝ) * P (i + p.1) (j + p.2) y) from funext ih]
    have hd : HasDerivAt
        (fun y => ∑ p ∈ Finset.antidiagonal m,
          (m.choose p.1 : ℝ) * P (i + p.1) (j + p.2) y)
        (∑ p ∈ Finset.antidiagonal m,
          (m.choose p.1 : ℝ) * deriv (P (i + p.1) (j + p.2)) x) x :=
      HasDerivAt.fun_sum fun p _ =>
        ((hP (i + p.1) (j + p.2)).differentiable (by simp) x).hasDerivAt.const_mul _
    rw [m62ArcDerivative, hd.deriv, Finset.mul_sum]
    calc
      (∑ p ∈ Finset.antidiagonal m, (curveSpeed F c t x)⁻¹ *
          ((m.choose p.1 : ℝ) * deriv (P (i + p.1) (j + p.2)) x)) =
          ∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℝ) *
            m62ArcDerivative F c t (P (i + p.1) (j + p.2)) x := by
        apply Finset.sum_congr rfl
        intro p _
        dsimp only [m62ArcDerivative]
        ring
      _ = (∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℝ) *
            P (i + p.1) (j + p.2 + 1) x) +
          ∑ p ∈ Finset.antidiagonal m, (m.choose p.1 : ℝ) *
            P (i + p.1 + 1) (j + p.2) x := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _
        rw [hpair]
        ring
      _ = ∑ p ∈ Finset.antidiagonal (m + 1), ((m + 1).choose p.1 : ℝ) *
          P (i + p.1) (j + p.2) x := by
        rw [Finset.sum_antidiagonal_choose_succ_mul
          (fun r s => P (i + r) (j + s) x) m]
        simp only [Nat.add_assoc]
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hp).symm]

theorem m63CurvatureJet_tangent_succ [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    (F.metric t).inner (c x t) (m63CurvatureJet F c (m + 1) t x)
      (spatialUnitTangent F c t x) =
      -(∑ j ∈ Finset.range (m + 1), ((m + 1).choose j : ℝ) *
        (F.metric t).inner (c x t) (m63CurvatureJet F c j t x)
          (m63CurvatureJet F c (m - j) t x)) := by
  let K : ℕ → (y : ℝ) → TangentSpace (𝓡 n) (c y t) := fun k =>
    match k with
    | 0 => spatialUnitTangent F c t
    | k + 1 => m63CurvatureJet F c k t
  have h := m63TangentJetPair_arc_iterate F c hc 1 0 (m + 1) ht x
  change ((m62ArcDerivative F c t)^[m + 1])
    (fun y => (F.metric t).inner (c y t) (K 1 y) (K 0 y)) x =
      ∑ p ∈ Finset.antidiagonal (m + 1), ((m + 1).choose p.1 : ℝ) *
        (F.metric t).inner (c x t) (K (1 + p.1) x) (K (0 + p.2) x) at h
  have horth : (fun y => (F.metric t).inner (c y t) (K 1 y) (K 0 y)) =
      (fun _ : ℝ => 0) := by
    funext y
    exact curvature_unitTangent_inner_zero F c hc (Ioo_subset_Icc_self ht) y
  have hzero (r : ℕ) : ((m62ArcDerivative F c t)^[r]) (fun _ : ℝ => 0) =
      (fun _ : ℝ => 0) := by
    induction r with
    | zero => rfl
    | succ r ih =>
      rw [Function.iterate_succ_apply', ih]
      funext y
      simp only [m62ArcDerivative, deriv_const, mul_zero]
  rw [horth, hzero, Finset.Nat.sum_antidiagonal_succ'] at h
  simp only [Nat.add_comm 1, Nat.zero_add, K, Nat.choose_self,
    Nat.cast_one, one_mul] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  linarith only [h]

theorem m63CurvatureJet_tangent_abs_le [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    |(F.metric t).inner (c x t) (m63CurvatureJet F c (m + 1) t x)
      (spatialUnitTangent F c t x)| ≤
      ∑ j ∈ Finset.range (m + 1), ((m + 1).choose j : ℝ) *
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c j t x) *
        (F.metric t).tangentNorm (c x t) (m63CurvatureJet F c (m - j) t x) := by
  let g := F.metric t
  let p := c x t
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hn (Z : TangentSpace (𝓡 n) p) : ‖Z‖ = g.tangentNorm p Z := by
    rw [norm_eq_sqrt_real_inner]
    rfl
  have hinner (U V : TangentSpace (𝓡 n) p) :
      |g.inner p U V| ≤ g.tangentNorm p U * g.tangentNorm p V := by
    change |inner ℝ U V| ≤ g.tangentNorm p U * g.tangentNorm p V
    simpa only [hn] using abs_real_inner_le_norm U V
  rw [m63CurvatureJet_tangent_succ F c hc m ht x, abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have h := mul_le_mul_of_nonneg_left
    (hinner (m63CurvatureJet F c j t x) (m63CurvatureJet F c (m - j) t x))
    (Nat.cast_nonneg ((m + 1).choose j) : (0 : ℝ) ≤ _)
  simpa only [mul_assoc] using h

end PoincareConjecture

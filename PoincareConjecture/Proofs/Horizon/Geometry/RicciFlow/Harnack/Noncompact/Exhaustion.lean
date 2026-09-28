import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Exhaustion.Transfer
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

structure SmoothExhaustion (F : RicciFlow n M J) (O : M) where
  toFun : M → ℝ
  smooth : ContMDiff (𝓡 n) (𝓘(ℝ, ℝ)) ∞ toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  distance_lower : ∀ t ∈ J, ∀ x,
    ENNReal.toReal ((F.metric t).edist O x) + 1 ≤ toFun x
  distance_upper : ∀ t ∈ J, ∀ x,
    toFun x ≤ bound * (ENNReal.toReal ((F.metric t).edist O x) + 1)
  gradient_bound : ∀ t ∈ J, ∀ x v,
    |mvfderiv (𝓡 n) toFun x v| ≤ bound * (F.metric t).tangentNorm x v
  hessian_bound : ∀ t ∈ J, ∀ x v,
    (F.connection t).hessian toFun x v v ≤ bound * (F.metric t).inner x v v

noncomputable def smoothExhaustionOfInitial
    (F : RicciFlow n M J) (O : M) (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (S : RiemannianMetric.SmoothDistanceLike
      (F.metric t₀) (F.connection t₀) O)
    (K A T : ℝ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hT : ∀ t ∈ J, |t - t₀| ≤ T)
    (hRic : ∀ t ∈ J, ∀ x (v : TangentSpace (𝓡 n) x),
      |(F.connection t).ricci x v v| ≤ K * (F.metric t).inner x v v)
    (hRicDeriv : ∀ t ∈ J, ∀ x (u v w : TangentSpace (𝓡 n) x),
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ A * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w) :
    SmoothExhaustion F O := by
  let E := Real.exp (K * T)
  let B := S.bound * (1 + 3 * A * E ^ 3 * T) * E ^ 2
  let C := 1 + S.bound * E ^ 2 + E * B
  have hS := S.bound_nonneg
  have hT₀ : 0 ≤ T := by simpa using hT t₀ ht₀
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdist : S.bound * E ^ 2 ≤ C := by
    dsimp only [C]
    linarith [mul_nonneg hE hB]
  have hhess : E * B ≤ C := by
    dsimp only [C]
    linarith [mul_nonneg hS (sq_nonneg E)]
  refine ⟨fun x => E * S.toFun x, contMDiff_const.mul S.smooth,
    C, hC, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    exact (F.distance_bounds_of_initial F.interval.convex (fun _ h => h)
      ht₀ ht O S K T hK (hT t ht) hRic x).1
  · intro t ht x
    exact (F.distance_bounds_of_initial F.interval.convex (fun _ h => h)
      ht₀ ht O S K T hK (hT t ht) hRic x).2.trans
        (mul_le_mul_of_nonneg_right hdist (by positivity))
  · intro t ht x v
    rw [mvfderiv_const_mul, abs_mul, abs_of_nonneg hE]
    have hg := F.gradient_bound_of_initial F.interval.convex (fun _ h => h)
      ht₀ ht O S K hRic x v
    have he : Real.exp (K * |t - t₀|) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hT t ht) hK)
    have hg' := hg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he hS) (Real.sqrt_nonneg _))
    calc
      E * |mvfderiv (𝓡 n) S.toFun x v| ≤
          E * (S.bound * E * (F.metric t).tangentNorm x v) :=
        mul_le_mul_of_nonneg_left hg' hE
      _ = (S.bound * E ^ 2) * (F.metric t).tangentNorm x v := by ring
      _ ≤ C * (F.metric t).tangentNorm x v :=
        mul_le_mul_of_nonneg_right hdist (Real.sqrt_nonneg _)
  · intro t ht x v
    rw [LeviCivitaData.hessian_const_mul]
    have h := F.hessian_bound_of_initial F.interval.convex (fun _ h => h)
      ht₀ ht O S K A T hK hA hT hRic hRicDeriv x v
    have hq : 0 ≤ (F.metric t).inner x v v := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨(F.metric t).toRiemannianMetric⟩
      change 0 ≤ inner ℝ v v
      exact real_inner_self_nonneg
    exact (mul_le_mul_of_nonneg_left h hE).trans
      (by simpa only [B, E, mul_assoc] using mul_le_mul_of_nonneg_right hhess hq)

lemma SmoothExhaustion.one_le {F : RicciFlow n M J} {O : M}
    (S : SmoothExhaustion F O) (x : M) : 1 ≤ S.toFun x := by
  obtain ⟨t, ht⟩ := F.nontrivial.nonempty
  exact (le_add_of_nonneg_left (ENNReal.toReal_nonneg)).trans
    (S.distance_lower t ht x)

lemma SmoothExhaustion.bound_pos {F : RicciFlow n M J} {O : M}
    (S : SmoothExhaustion F O) : 0 < S.bound := by
  obtain ⟨t, ht⟩ := F.nontrivial.nonempty
  have h := S.distance_upper t ht O
  have h₁ := S.one_le O
  by_contra hpos
  have hzero : S.bound = 0 := le_antisymm (le_of_not_gt hpos) S.bound_nonneg
  rw [hzero, zero_mul] at h
  linarith

lemma SmoothExhaustion.laplacian_le {F : RicciFlow n M J} {O : M}
    (S : SmoothExhaustion F O) {t : ℝ} (ht : t ∈ J) (x : M) :
    (F.connection t).laplacian S.toFun x ≤ (n : ℝ) * S.bound := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let b := (F.metric t).orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
  have hinner (i) : (F.metric t).inner x (b i) (b i) = 1 := by
    change inner ℝ (b i) (b i) = 1
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i, one_pow]
  calc
    (F.connection t).laplacian S.toFun x ≤ ∑ i, S.bound :=
      Finset.sum_le_sum fun i _ => by simpa only [hinner i, mul_one] using S.hessian_bound t ht x (b i)
    _ = (n : ℝ) * S.bound := by simp [hdim]

lemma LeviCivitaData.laplacian_const_mul {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (c : ℝ) (f : M → ℝ) (x : M) :
    D.laplacian (fun y => c * f y) x = c * D.laplacian f x := by
  unfold LeviCivitaData.laplacian
  simp only [LeviCivitaData.hessian_const_mul]
  rw [Finset.mul_sum]

noncomputable def smoothExhaustionOfInitialOfCurvatureBound [T2Space M]
    (F : RicciFlow n M J) (O : M) (t₀ : ℝ) (ht₀ : t₀ ∈ J)
    (S : RiemannianMetric.SmoothDistanceLike (F.metric t₀) (F.connection t₀) O)
    (k₀ A T : ℝ) (hk₀ : 0 ≤ k₀) (hA : 0 ≤ A)
    (hT : ∀ t ∈ J, |t - t₀| ≤ T)
    (hRm : ∀ t ∈ J, ∀ x, (F.connection t).curvatureTensorNorm x ≤ k₀)
    (hRicDeriv : ∀ t ∈ J, ∀ x (u v w : TangentSpace (𝓡 n) x),
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ A * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w) :
    SmoothExhaustion F O := by
  apply F.smoothExhaustionOfInitial O t₀ ht₀ S ((n : ℝ) ^ 3 * k₀) A T
    (by positivity) hA hT ?_ hRicDeriv
  intro t ht x v
  have hQ : 0 ≤ (F.metric t).inner x v v := by
    by_cases hv : v = 0
    · subst v; simp
    · exact ((F.metric t).pos x v hv).le
  have hnorm := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm x v
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := finrank_euclideanSpace_fin
  simp only [Fintype.card_fin, hdim] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hRm t ht x) (by positivity)) hQ)

theorem exists_smoothExhaustion_of_curvature_bound
    [T3Space M] [PreconnectedSpace M] [NoncompactSpace M]
    (F : RicciFlow n M J) (t₀ T k₀ : ℝ) (ht₀ : t₀ ∈ J)
    (hT : ∀ t ∈ J, |t - t₀| ≤ T)
    (hcomplete : ∀ t ∈ J, MetricComplete (F.metric t))
    (hk₀ : 0 ≤ k₀)
    (hRm : ∀ t ∈ J, ∀ x, (F.connection t).curvatureTensorNorm x ≤ k₀)
    (hRicDeriv : ∀ t ∈ J, ∀ x (u v w : TangentSpace (𝓡 n) x),
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ k₀ * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w) :
    ∃ C : ℝ, 0 < C ∧ ∀ O : M, ∃ S : SmoothExhaustion F O, S.bound = C := by
  obtain ⟨C₀, hC₀, hinitial⟩ :=
    RiemannianMetric.exists_uniform_smoothDistanceLike n hk₀
  let K : ℝ := (n : ℝ) ^ 3 * k₀
  let E : ℝ := Real.exp (K * T)
  let C : ℝ := 1 + C₀ * E ^ 2 +
    E * (C₀ * (1 + 3 * k₀ * E ^ 3 * T) * E ^ 2)
  have hT₀ : 0 ≤ T := by simpa using hT t₀ ht₀
  have hC : 0 < C := by
    dsimp only [C]
    have hE : 0 ≤ E := Real.exp_nonneg _
    have hB : 0 ≤ C₀ * (1 + 3 * k₀ * E ^ 3 * T) * E ^ 2 := by
      positivity
    positivity
  refine ⟨C, hC, ?_⟩
  intro O
  obtain ⟨S, hS⟩ := hinitial (F.metric t₀) (F.connection t₀)
    (hcomplete t₀ ht₀) (hRm t₀ ht₀) O
  let H := F.smoothExhaustionOfInitialOfCurvatureBound O t₀ ht₀ S
    k₀ k₀ T hk₀ hk₀ hT hRm hRicDeriv
  refine ⟨H, ?_⟩
  dsimp only [H, smoothExhaustionOfInitialOfCurvatureBound,
    smoothExhaustionOfInitial, C, E, K]
  simp only [hS]

end PoincareConjecture.RicciFlow

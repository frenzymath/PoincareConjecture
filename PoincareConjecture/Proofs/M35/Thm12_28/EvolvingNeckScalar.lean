import PoincareConjecture.Proofs.M35.Thm12_28.NeckScalarEstimates
import PoincareConjecture.Proofs.M35.Thm12_28.ParabolicScalar
import PoincareConjecture.Proofs.M35.RawFlow.Completeness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35




theorem exists_half_neck_scalar_bounds (P : M35StandardCapPredecessors) :
    ∃ delta A : ℝ, 0 < delta ∧ 0 < A ∧
      ∀ epsilon : ℝ, epsilon ≤ delta →
        ∀ (atlas : StandardCylinderAtlas) (g₀ : StandardInitialMetric)
          (F : MaximalStandardCapFlow g₀) (t : ℝ) (x : StandardCapSpace) (I : Set ℝ)
          (_N : StandardEvolvingNeck atlas F t epsilon x I), Icc (-(1 / 2) : ℝ) 0 ⊆ I →
          (∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
            |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤
              A * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
          |(F.connection t).laplacian (F.connection t).scalarCurvature x +
              2 * (F.connection t).ricciNormSq x| ≤
            A * ((F.connection t).scalarCurvature x) ^ 2 := by
  obtain ⟨delta, A, hdelta, hA, hbounds⟩ := exists_short_neck_scalar_bounds P.curvature
  refine ⟨delta, A, hdelta, hA, ?_⟩
  intro epsilon hedelta atlas g₀ F t x I N hretained
  let Q := (F.connection t).scalarCurvature x
  have hQ : 0 < Q := N.scalar_pos
  let J : SpacetimeInterval :=
    ⟨Ico 0 F.base.lifetime, F.base.flow.interval, F.base.flow.nontrivial⟩
  obtain ⟨R⟩ := P.ordinary_flow StandardCapSpace J F.base.flow Q hQ (t - (1 / 2) / Q)
  have hclock (s : ℝ) : parabolicTimeInv Q (t - (1 / 2) / Q) s = t + (s - 1 / 2) / Q := by
    unfold parabolicTimeInv
    ring
  have htop : parabolicTimeInv Q (t - (1 / 2) / Q) (1 / 2) = t := by rw [hclock]; ring
  have hsub : Icc (0 : ℝ) (1 / 2) ⊆ (parabolicInterval Q hQ (t - (1 / 2) / Q) J).domain := by
    intro s hs
    apply (mem_parabolicInterval_iff Q hQ (t - (1 / 2) / Q) J s).mpr
    rw [hclock]
    exact N.interval_survival (s - 1 / 2) (hretained ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow R.flow hsub
    ordConnected_Icc ⟨0, by norm_num, 1 / 2, by norm_num, by norm_num⟩
  have hcomplete : MetricComplete (G.metric 0) := by
    apply (R.metric_calculus 0).complete_iff.mpr
    exact F.base.complete P.curvature
      ((mem_parabolicInterval_iff Q hQ (t - (1 / 2) / Q) J 0).mp (hsub (by norm_num)))
  have hpull (s : ℝ) : roundCylinderPullback (G.metric s) N.patch.coordinate =
      fun z v w => Q * roundCylinderPullback (F.metric (t + (s - 1 / 2) / Q))
        N.patch.coordinate z v w := by
    funext z v w
    unfold roundCylinderPullback
    change (R.flow.metric s).inner _ _ _ = Q * (F.metric (t + (s - 1 / 2) / Q)).inner _ _ _
    rw [R.metric_eq, hclock]
    rfl
  have hclose (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
      RoundCylinderClose epsilon (s - 1 / 2)
        (roundCylinderPullback (G.metric s) N.patch.coordinate) := by
    rw [hpull]
    obtain ⟨hsmooth, b, hb, hjet⟩ := N.close
    have hu : s - 1 / 2 ∈ I := hretained ⟨by linarith [hs.1], by linarith [hs.2]⟩
    exact ⟨hsmooth (s - 1 / 2) hu, b, hb, hjet (s - 1 / 2) hu⟩
  obtain ⟨hspace, htime⟩ := hbounds epsilon N.epsilon_pos hedelta
    (1 / 2) (by norm_num) (by norm_num) G x N.patch hcomplete hclose
  constructor
  · intro v hv
    have hn : (G.metric (1 / 2)).tangentNorm x v = Real.sqrt Q := by
      change Real.sqrt ((R.flow.metric (1 / 2)).inner x v v) = Real.sqrt Q
      rw [R.metric_eq, htop]
      change Real.sqrt (Q * (F.metric t).inner x v v) = Real.sqrt Q
      rw [hv, mul_one]
    have hd := hspace v
    rw [hn] at hd
    change |mvfderiv (𝓡 3) (R.flow.connection (1 / 2)).scalarCurvature x v| ≤ A * Real.sqrt Q at hd
    rw [R.scalar_directional_eq, htop, abs_div, abs_of_pos hQ] at hd
    have hp : Q ^ (3 / 2 : ℝ) = Q * Real.sqrt Q := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hQ,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    change |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤ A * Q ^ (3 / 2 : ℝ)
    calc
      _ ≤ A * Real.sqrt Q * Q := (div_le_iff₀ hQ).mp hd
      _ = _ := by rw [hp]; ring
  · change |(R.flow.connection (1 / 2)).laplacian (R.flow.connection (1 / 2)).scalarCurvature x +
        2 * (R.flow.connection (1 / 2)).ricciNormSq x| ≤ A at htime
    rw [R.scalar_evolution_eq_of_interval P.curvature (by norm_num) hsub x, htop, abs_div,
      abs_of_nonneg (sq_nonneg Q)] at htime
    exact (div_le_iff₀ (sq_pos_of_pos hQ)).mp htime




theorem exists_evolving_neck_scalar_bounds (P : M35StandardCapPredecessors) :
    ∃ delta A : ℝ, 0 < delta ∧ 0 < A ∧
      ∀ epsilon : ℝ, epsilon ≤ delta →
        ∀ (atlas : StandardCylinderAtlas) (g₀ : StandardInitialMetric)
          (F : MaximalStandardCapFlow g₀) (t : ℝ) (x : StandardCapSpace) (I : Set ℝ)
          (_N : StandardEvolvingNeck atlas F t epsilon x I), Icc (-1 : ℝ) 0 ⊆ I →
          (∀ v : TangentSpace (𝓡 3) x, (F.metric t).inner x v v = 1 →
            |mvfderiv (𝓡 3) (F.connection t).scalarCurvature x v| ≤
              A * (F.connection t).scalarCurvature x ^ (3 / 2 : ℝ)) ∧
          |(F.connection t).laplacian (F.connection t).scalarCurvature x +
              2 * (F.connection t).ricciNormSq x| ≤
            A * ((F.connection t).scalarCurvature x) ^ 2 := by
  obtain ⟨delta, A, hdelta, hA, hbound⟩ := exists_half_neck_scalar_bounds P
  refine ⟨delta, A, hdelta, hA, ?_⟩
  intro epsilon he atlas g₀ F t x I N hretained
  apply hbound epsilon he atlas g₀ F t x I N
  intro u hu
  exact hretained ⟨by linarith [hu.1], hu.2⟩

end PoincareConjecture.M35

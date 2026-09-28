import PoincareConjecture.Proofs.M47.PositiveGradientMetric
import PoincareConjecture.Proofs.M47.PositiveGradientMyers










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric 3 M}





theorem half_scalar_lower_of_small_gradient (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hc : MetricComplete g) (p : M)
    {delta Q : ℝ} (hdelta : 0 < delta) (hQ : 0 < Q) (hp : D.scalarCurvature p = Q)
    (hgradient : ∀ y, g.inner y (D.gradient D.scalarCurvature y)
      (D.gradient D.scalarCurvature y) ≤ (delta / 320) * Q ^ 3)
    (hRic : ∀ y (v : TangentSpace (𝓡 3) y),
      delta * D.scalarCurvature y * g.inner y v v ≤ D.ricci y v v) :
    ∀ x : M, Q / 2 ≤ D.scalarCurvature x := by
  let A := Real.sqrt ((delta / 320) * Q ^ 3)
  let rho := Real.sqrt (80 / (delta * Q))
  have hA : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hrho : 0 < rho := Real.sqrt_pos.mpr (by positivity)
  have hAsq : A ^ 2 = (delta / 320) * Q ^ 3 := Real.sq_sqrt (by positivity)
  have hrhosq : rho ^ 2 = 80 / (delta * Q) := Real.sq_sqrt (by positivity)
  have hproduct : A * rho = Q / 2 := by
    apply (sq_eq_sq₀ (mul_nonneg hA.le hrho.le) (by positivity)).mp
    rw [mul_pow, hAsq, hrhosq]
    field_simp [hdelta.ne', hQ.ne']
    ring
  have hLip (y : M) : |Q - D.scalarCurvature y| ≤ A * (g.edist p y).toReal := by
    have h := scalar_increment_le_of_gradient_energy_bound D hD.contMDiff_scalarCurvature
      hA (fun z => by rw [hAsq]; exact hgradient z) p y
    rwa [hp] at h
  have hlocal (y : M) (hy : (g.edist p y).toReal ≤ rho) : Q / 2 ≤ D.scalarCurvature y := by
    have h := (hLip y).trans (mul_le_mul_of_nonneg_left hy hA.le)
    rw [hproduct] at h
    have hle := le_abs_self (Q - D.scalarCurvature y)
    linarith only [h, hle]
  have hball (x : M) : (g.edist p x).toReal < rho := by
    by_contra hx
    obtain ⟨y, hy⟩ := exists_point_at_intrinsic_radius g hc p x hrho (le_of_not_gt hx)
    have hmyers := ricci_distance_sq_le_of_ball_lower g D hc p y (k := delta * Q / 2) (by
      intro z hz v
      have hzR := hlocal z (hz.trans_eq hy)
      have hv : 0 ≤ g.inner z v v := by
        by_cases hv : v = 0
        · simp [hv]
        · exact (g.pos z v hv).le
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzR hdelta.le) hv
      have hlower := hRic z v
      nlinarith only [h, hlower])
    rw [hy, hrhosq] at hmyers
    have hid : delta * Q / 2 * (80 / (delta * Q)) = 40 := by
      field_simp [hdelta.ne', hQ.ne']
      ring
    rw [hid] at hmyers
    norm_num at hmyers
  exact fun x => hlocal x (hball x).le





theorem exists_scalar_maximum_uniformization_threshold
    [CompactSpace M] [SecondCountableTopology M]
    (hC : RicciFlowCurvatureTheory.{u}) {T : ℝ} (hT : 0 < T)
    (F : RicciFlow 3 M (Ico 0 T))
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
        0 < (F.connection 0).sectionalCurvature x v w) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ t ∈ Ico 0 T, ∀ p : M,
      B ≤ (F.connection t).scalarCurvature p →
      (∀ y, (F.connection t).scalarCurvature y ≤ (F.connection t).scalarCurvature p) →
      ∀ x, (F.connection t).scalarCurvature p / 2 ≤ (F.connection t).scalarCurvature x := by
  obtain ⟨delta, hdelta, _, hpinch⟩ := exists_uniform_ricci_pinching hC hT F hpos
  let eta := delta / 640
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨K, _, hgradient⟩ := exists_uniform_scalar_gradient_bound hC hT F hpos heta
  obtain ⟨r, hr, hlower⟩ := exists_uniform_positive_scalar_lower hT F hpos
  let B := max 1 (K / eta)
  refine ⟨B, le_max_left _ _, ?_⟩
  intro t ht p hp hmax x
  let D := F.connection t
  let Q := D.scalarCurvature p
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans hp
  have hQ : 0 < Q := (by norm_num : (0 : ℝ) < 1).trans_le hQ1
  have hKQ : K ≤ Q * eta := (div_le_iff₀ heta).mp ((le_max_right _ _).trans hp)
  have hQcube : Q ≤ Q ^ 3 := by nlinarith only [hQ1, sq_nonneg (Q - 1)]
  have hKcube : K ≤ eta * Q ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hQcube heta.le
    nlinarith only [hKQ, h]
  apply half_scalar_lower_of_small_gradient D
    (hC.tensor_calculus 3 M (F.metric t) D) (F.metric t).metricComplete_of_compact p hdelta hQ rfl
  · intro y
    have hRy : 0 ≤ D.scalarCurvature y := (hr.trans_le (hlower t ht y)).le
    have hcube : D.scalarCurvature y ^ 3 ≤ Q ^ 3 := by gcongr; exact hmax y
    have h := hgradient t ht y
    have hmul := mul_le_mul_of_nonneg_left hcube heta.le
    change _ ≤ (delta / 320) * Q ^ 3
    dsimp only [eta] at h hmul hKcube
    nlinarith only [h, hmul, hKcube]
  · intro y v
    exact ricci_lower_of_unit_lower D y (hpinch t ht y) v

end PoincareConjecture.M47Positive

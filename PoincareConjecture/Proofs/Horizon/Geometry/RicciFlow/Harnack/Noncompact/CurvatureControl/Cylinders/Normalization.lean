import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.TimeBuffer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Cylinders










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow



theorem curvatureTensorNorm_le_on_two_time_ball_of_terminal_cylinder
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a b L S : ℝ} (hJ : Icc a b ⊆ interior J)
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (p : M)
    (hscalar : ∀ t ∈ Icc a b, ∀ x ∈ (F.metric b).ball p L,
      (F.connection t).scalarCurvature x ≤ S)
    {s t ρ : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hρ : ρ ≤ L)
    (x : M) (hx : x ∈ (F.metric s).ball p ρ) :
    (F.connection t).curvatureTensorNorm x ≤ (n : ℝ) ^ 2 * S := by
  have hRic (q : ℝ) (hq : q ∈ Icc a b) (y : M) (v : TangentSpace (𝓡 n) y) :
      0 ≤ (F.connection q).ricci y v v :=
    ((F.connection q).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M (F.metric q) (F.connection q)) y (hoperator q hq y) v).1
  have hxterminal := F.ball_subset_ball_of_ricci_nonneg hJ p ρ hs
    ⟨hs.1.trans hs.2, le_rfl⟩ hs.2 (fun q hq y _ v => hRic q hq y v) hx
  have hxL : x ∈ (F.metric b).ball p L :=
    hxterminal.trans_le (ENNReal.ofReal_le_ofReal hρ)
  exact ((F.connection t).curvatureTensorNorm_le_scalarCurvature
    (hC.tensor_calculus n M (F.metric t) (F.connection t)) x (hoperator t ht x)).trans
      (mul_le_mul_of_nonneg_left (hscalar t ht x hxL) (sq_nonneg _))



theorem exists_terminal_scalar_positive_scale_buffer
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] (J : Set ℝ)
        (F : RicciFlow (m + 1) M J) (Q τ : ℝ),
        0 < Q → Icc (τ - 2 / Q) τ ⊆ interior J →
        (∀ t ∈ Icc (τ - 2 / Q) τ, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc (τ - 2 / Q) τ, ∀ x : M,
          (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
          (∀ t ∈ Icc (τ - 2 / Q) τ,
            ∀ x ∈ (F.metric τ).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8) / Real.sqrt Q),
              (F.connection t).scalarCurvature x ≤ 4 * Q) →
          (F.connection τ).scalarCurvature p = Q →
          ∀ t ∈ Icc (τ - δ / Q) τ,
            Q / 2 ≤ (F.connection t).scalarCurvature p := by
  obtain ⟨δ, hδ, hδone, hbuffer⟩ := exists_terminal_scalar_positive_time_buffer hC hm
  refine ⟨δ, hδ, hδone, ?_⟩
  intro M _ _ _ _ _ J F Q τ hQ hJ hcomplete hoperator p hscalar hnormalize t ht
  let K : Set ℝ := (fun s : ℝ => τ + s / Q) ⁻¹' J
  have hmap (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 0) :
      τ + s / Q ∈ Icc (τ - 2 / Q) τ := rescalingTime_mem_Icc hQ τ 2 hs
  have hK : K.OrdConnected := F.interval.preimage_mono
    (fun _ _ h => _root_.add_le_add le_rfl (div_le_div_of_nonneg_right h hQ.le))
  have hsub : Icc (-2 : ℝ) 0 ⊆ K := fun s hs =>
    (show τ + s / Q ∈ J from interior_subset (hJ (hmap s hs)))
  have hne : K.Nontrivial :=
    ⟨-2, hsub (by norm_num), 0, hsub (by norm_num), by norm_num⟩
  let G := F.parabolicRescale Q hQ τ (K := K) (fun _ hs => hs) hK hne
  have hGJ : Icc (-2 : ℝ) 0 ⊆ interior K := by
    intro s hs
    apply preimage_interior_subset_interior_preimage
      (show Continuous (fun s : ℝ => τ + s / Q) by fun_prop)
    exact hJ (hmap s hs)
  have hGcomplete (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 0) : MetricComplete (G.metric s) :=
    F.parabolicRescale_metricComplete Q hQ τ _ hK hne s (hcomplete _ (hmap s hs))
  have hGoperator (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 0) (x : M) :
      (G.connection s).NonnegativeCurvatureOperator x :=
    F.parabolicRescale_nonnegativeCurvatureOperator Q hQ τ _ hK hne s x
      (hoperator _ (hmap s hs) x)
  have hGscalar (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 0) (x : M)
      (hx : x ∈ (G.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8))) :
      (G.connection s).scalarCurvature x ≤ 4 := by
    change x ∈ (rescaledMetric (F.metric (τ + 0 / Q)) Q hQ).ball p _ at hx
    rw [rescaledMetric_ball_allDimensions, zero_div, add_zero] at hx
    change (rescaledMetric_connection _ _ Q hQ).scalarCurvature x ≤ 4
    rw [rescaledMetric_scalarCurvature]
    have h := mul_le_mul_of_nonneg_left (hscalar _ (hmap s hs) x hx)
      (inv_nonneg.mpr hQ.le)
    calc
      Q⁻¹ * (F.connection (τ + s / Q)).scalarCurvature x ≤ Q⁻¹ * (4 * Q) := h
      _ = 4 := by field_simp
  have hGnormalize : (G.connection 0).scalarCurvature p = 1 := by
    change (rescaledMetric_connection _ _ Q hQ).scalarCurvature p = 1
    rw [rescaledMetric_scalarCurvature, zero_div, add_zero, hnormalize, inv_mul_cancel₀ hQ.ne']
  have hs : Q * (t - τ) ∈ Icc (-δ) 0 := by
    constructor
    · have h := (le_div_iff₀ hQ).mp (show τ - t ≤ δ / Q by linarith [ht.1])
      nlinarith
    · exact mul_nonpos_of_nonneg_of_nonpos hQ.le (sub_nonpos.mpr ht.2)
  have h := hbuffer M K G hGJ hGcomplete hGoperator p hGscalar hGnormalize _ hs
  change (1 : ℝ) / 2 ≤ (rescaledMetric_connection _ _ Q hQ).scalarCurvature p at h
  rw [rescaledMetric_scalarCurvature] at h
  have htime : τ + Q * (t - τ) / Q = t := by field_simp; ring
  rw [htime, ← div_eq_inv_mul] at h
  have h' := (le_div_iff₀ hQ).mp h
  linarith

end PoincareConjecture.RicciFlow

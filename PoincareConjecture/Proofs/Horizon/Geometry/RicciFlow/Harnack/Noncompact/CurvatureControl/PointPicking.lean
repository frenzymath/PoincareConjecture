import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.PointPicking
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Theory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.MetricMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem exists_scalarCurvature_point_with_doubling_bound
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    {a b : ℝ} (hJ : Icc a b ⊆ interior J)
    (hcomplete : MetricComplete (F.metric b))
    (hRic : ∀ t ∈ Icc a b, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      0 ≤ (F.connection t).ricci x v v)
    (p : M) (r : ℝ) {L : ℝ} (hL : 0 ≤ L)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a b) {x₀ : M}
    (hx₀ : x₀ ∈ (F.metric t₀).ball p r)
    (hR₀ : 0 < (F.connection t₀).scalarCurvature x₀) :
    ∃ t ∈ Icc a t₀, ∃ x ∈ (F.metric t).ball p r,
      (F.connection t₀).scalarCurvature x₀ ≤ (F.connection t).scalarCurvature x ∧
      ((F.metric t).edist p x).toReal +
          2 * L / Real.sqrt ((F.connection t).scalarCurvature x) ≤
        ((F.metric t₀).edist p x₀).toReal +
          2 * L / Real.sqrt ((F.connection t₀).scalarCurvature x₀) ∧
      ∀ s ∈ Icc a t, ∀ y ∈ (F.metric s).ball p r,
        ((F.metric s).edist p y).toReal ≤ ((F.metric t).edist p x).toReal +
          L / Real.sqrt ((F.connection t).scalarCurvature x) →
        (F.connection s).scalarCurvature y ≤ 4 * (F.connection t).scalarCurvature x := by
  let S : Set (ℝ × M) := {z | z.1 ∈ Icc a b ∧ z.2 ∈ (F.metric z.1).ball p r}
  let K : Set (ℝ × M) := Icc a b ×ˢ {x | (F.metric b).edist p x ≤ ENNReal.ofReal r}
  let q : ℝ × M → ℝ := fun z => Real.sqrt ((F.connection z.1).scalarCurvature z.2)
  let radius : ℝ × M → ℝ := fun z => ((F.metric z.1).edist p z.2).toReal
  have hb : b ∈ Icc a b := ⟨ht₀.1.trans ht₀.2, le_rfl⟩
  have hSK : S ⊆ K := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    refine ⟨hs, ?_⟩
    have hball := F.ball_subset_ball_of_ricci_nonneg hJ p r hs hb hs.2
      (fun t ht x _ v => hRic t ht x v) hy
    exact (show (F.metric b).edist p y < ENNReal.ofReal r from hball).le
  have hK : IsCompact K := isCompact_Icc.prod
    ((F.metric b).isCompact_closedBall_of_metricComplete hcomplete p r)
  have hq : ContinuousOn q K := Real.continuous_sqrt.comp_continuousOn
    ((hC.scalar_regular n M J F).continuousOn.mono (fun z hz =>
      ⟨interior_subset (hJ hz.1), mem_univ _⟩))
  have hbound : BddAbove (q '' S) := (hK.bddAbove_image hq).mono (image_mono hSK)
  obtain ⟨⟨t, x⟩, htx, htt, hRx, hrad, hlocal⟩ :=
    Poincare.Parabolic.exists_point_with_doubling_bound S q radius Prod.fst hbound hL
      (show (t₀, x₀) ∈ S from ⟨ht₀, hx₀⟩) (Real.sqrt_pos.mpr hR₀)
  have hR (s : ℝ) (hs : s ∈ Icc a b) (y : M) :
      0 ≤ (F.connection s).scalarCurvature y :=
    Finset.sum_nonneg (fun i _ => hRic s hs y _)
  have hRx' : (F.connection t₀).scalarCurvature x₀ ≤
      (F.connection t).scalarCurvature x := by
    have hsq := sq_le_sq₀ (Real.sqrt_nonneg ((F.connection t₀).scalarCurvature x₀))
      (Real.sqrt_nonneg ((F.connection t).scalarCurvature x))
    simpa only [Real.sq_sqrt hR₀.le, Real.sq_sqrt (hR t htx.1 x)] using hsq.mpr hRx
  refine ⟨t, ⟨htx.1.1, htt⟩, x, htx.2, hRx', hrad, ?_⟩
  intro s hs y hy hdist
  have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans htx.1.2⟩
  have h := hlocal (s, y) ⟨hs', hy⟩ hs.2 hdist
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg ((F.connection s).scalarCurvature y)) h
  dsimp only [q] at hsq
  nlinarith [Real.sq_sqrt (hR s hs' y), Real.sq_sqrt (hR t htx.1 x)]

end PoincareConjecture.RicciFlow

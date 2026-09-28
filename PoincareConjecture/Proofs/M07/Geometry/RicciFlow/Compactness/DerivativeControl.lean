import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Curvature.Estimates.Local
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.LocalGeometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormBounds










set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

open Set

theorem eventually_zero_time_curvatureDerivativeNorm_le_of_local_derivative_estimates
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ x ∈ F.zeroBall A,
        (F.flow.connection 0).curvatureDerivativeNorm m x ≤ D := by
  obtain ⟨KA, hKA, hAevent⟩ := H.all_time_curvature_control A hA
  obtain ⟨K4, hK4, h4event⟩ := H.all_time_curvature_control (4 * A) (by positivity)
  let LA : ℝ := (n : ℝ) ^ 3 * KA
  let K0 : ℝ := K4 + 1
  let l2 : ℝ := Real.log 2
  let q : ℝ := min (-T') (min T (min (1 / K0) (l2 / (LA + 1))))
  let δ : ℝ := q / 2
  have hK0 : 0 < K0 := by dsimp [K0]; linarith
  have hl2 : 0 < l2 := Real.log_pos (by norm_num)
  have hT' : T' < 0 := H.time_bounds.1
  have hT : 0 < T := H.time_bounds.2
  have hLA : 0 ≤ LA := by
    dsimp [LA]
    positivity
  have hq : 0 < q := by
    dsimp [q]
    refine lt_min (by linarith) (lt_min hT (lt_min (by positivity) (by positivity)))
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδT' : δ < -T' := by
    have hq' : q ≤ -T' := min_le_left _ _
    dsimp [δ]
    linarith
  have hδT : δ < T := by
    have hq' : q ≤ T := by
      dsimp [q]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    dsimp [δ]
    linarith
  have hδK : δ ≤ 1 / K0 := by
    have hq' : q ≤ 1 / K0 := by
      dsimp [q]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    dsimp [δ]
    linarith
  have hδL : LA * δ ≤ l2 := by
    have hq' : q ≤ l2 / (LA + 1) := by
      dsimp [q]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hqbound : LA * q ≤ l2 := by
      calc
        LA * q ≤ LA * (l2 / (LA + 1)) :=
          mul_le_mul_of_nonneg_left hq' hLA
        _ ≤ l2 := by
          calc
            LA * (l2 / (LA + 1)) ≤ (LA + 1) * (l2 / (LA + 1)) := by
              gcongr
              linarith
            _ = l2 := by field_simp
    dsimp [δ]
    nlinarith
  obtain ⟨Cderiv, hCderiv, hShi⟩ :=
    hShi n m K0 1 (4 * A)
      (by linarith) (by norm_num) (by linarith)
  refine ⟨Cderiv / δ ^ ((m : ℝ) / 2), by positivity, ?_⟩
  filter_upwards [hAevent, h4event, H.eventually_all_time_ball_compact (4 * A) (by positivity)]
    with k hkA hk4 hkcompact
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T2Space C.carrier := C.t2Space
  letI : SecondCountableTopology C.carrier := C.secondCountable
  have hshift : (fun t : ℝ ↦ t + (-δ)) '' Icc 0 δ ⊆ Ioo T' T := by
    rintro _ ⟨t, ht, rfl⟩
    constructor <;> dsimp
    · linarith [ht.1]
    · linarith [ht.2]
  have hneIcc : (Icc (0 : ℝ) δ).Nontrivial := by
    exact ⟨0, ⟨le_rfl, hδ.le⟩, δ, ⟨hδ.le, le_rfl⟩, (ne_of_gt hδ).symm⟩
  let Ft := PoincareConjecture.RicciFlow.translate F.flow (-δ) hshift
      Set.ordConnected_Icc hneIcc
  have hcompact : IsCompact (closure ((Ft.metric 0).ball F.base (4 * A))) := by
    rw [PoincareConjecture.RicciFlow.translate_metric F.flow (-δ) hshift
      Set.ordConnected_Icc hneIcc 0]
    simpa only [BasedFlow.ballAt, FlowCarrier.metricBall, zero_add] using
      hkcompact (-δ) ⟨by linarith, by linarith⟩
  have hcurv : ∀ t ∈ Icc 0 δ, ∀ x ∈ (Ft.metric 0).ball F.base (4 * A),
      (Ft.connection t).curvatureTensorNorm x ≤ K0 := by
    intro t ht x hx
    have htx : x ∈ F.ballAt (-δ) (4 * A) := by
      change x ∈ (F.flow.metric (-δ)).ball F.base (4 * A)
      simpa [Ft, PoincareConjecture.RicciFlow.translate] using hx
    exact le_trans (hk4 (-δ) ⟨by linarith, by linarith⟩ (t + (-δ))
      (hshift ⟨t, ht, rfl⟩) x htx) (by linarith)
  have htime := hShi C.carrier δ hδ hδK Ft F.base hcompact hcurv
  have hderiv := htime δ ⟨by linarith, le_rfl⟩
  change ∀ x : C.carrier, x ∈ F.zeroBall A →
    (F.flow.connection 0).curvatureDerivativeNorm m x ≤ Cderiv / δ ^ ((m : ℝ) / 2)
  intro x hx
  change x ∈ (F.flow.metric 0).ball F.base A at hx
  have hRic : ∀ τ ∈ Ioo T' T, ∀ y ∈ F.zeroBall A,
      ∀ v : C.tangent y,
        |(F.flow.connection τ).ricci y v v| ≤ LA * (F.flow.metric τ).inner y v v := by
    intro τ hτ y hy v
    have hQ : 0 ≤ (F.flow.metric τ).inner y v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.flow.metric τ).pos y v hv).le
    have hnorm := (F.flow.connection τ).abs_ricci_quadratic_le_curvatureTensorNorm y v
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) y) = n := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hkA 0 ⟨H.time_bounds.1, H.time_bounds.2⟩ τ hτ y hy)
        (by positivity)) hQ)
  have hball := F.flow.ball_subset_ball_of_ricci_bound (convex_Ioo T' T)
    (Set.Subset.refl _) F.base A LA (s := 0) (t := -δ)
    ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hRic
  have hx2 : x ∈ (F.flow.metric (-δ)).ball F.base (2 * A) := by
    have hx' := hball hx
    change (F.flow.metric (-δ)).edist F.base x < ENNReal.ofReal (2 * A)
    change x ∈ (F.flow.metric 0).ball F.base A at hx
    have hexp : Real.exp (LA * δ) ≤ 2 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hδL
    have hrad : Real.exp (LA * δ) * A ≤ 2 * A := by nlinarith
    have habs : |-δ - 0| = δ := by
      simp [abs_of_neg (by linarith : -δ < 0)]
    rw [habs] at hx'
    exact lt_of_lt_of_le hx' (ENNReal.ofReal_le_ofReal hrad)
  have hx2' : x ∈ (Ft.metric 0).ball F.base (4 * A / 2) := by
    rw [PoincareConjecture.RicciFlow.translate_metric F.flow (-δ) hshift
      Set.ordConnected_Icc hneIcc 0]
    convert hx2 using 1 <;> ring
  have h := hderiv x hx2'
  have hnorm : (Ft.connection δ).curvatureDerivativeNorm m x =
      (F.flow.connection 0).curvatureDerivativeNorm m x := by
    change (F.flow.connection (δ + -δ)).curvatureDerivativeNorm m x =
      (F.flow.connection 0).curvatureDerivativeNorm m x
    rw [add_neg_cancel]
  rw [hnorm] at h
  exact h


theorem eventually_zero_time_curvatureDerivativeNorm_le
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0})
    (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ x ∈ F.zeroBall A,
        (F.flow.connection 0).curvatureDerivativeNorm m x ≤ D :=
  H.eventually_zero_time_curvatureDerivativeNorm_le_of_local_derivative_estimates
    hM04.local_derivative_estimates A hA m

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses

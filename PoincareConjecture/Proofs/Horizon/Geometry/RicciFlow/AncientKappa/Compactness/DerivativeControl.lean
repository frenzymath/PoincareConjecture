import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.LocalGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.NormBounds

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

open Set

theorem eventually_interior_curvatureDerivativeNorm_le_of_m23_predecessors
    {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors)
    (a b : ℝ) (ha : T' < a) (hb : b < T)
    (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
      ∀ t ∈ Icc a b, ∀ x ∈ F.ballAt t A,
        (F.flow.connection t).curvatureDerivativeNorm m x ≤ D := by
  obtain ⟨KA, hKA, hAevent⟩ := H.all_time_curvature_control A hA
  obtain ⟨K4, hK4, h4event⟩ := H.all_time_curvature_control (4 * A) (by positivity)
  let L : ℝ := (3 : ℝ) ^ 3 * KA
  let K0 : ℝ := K4 + 1
  let l2 : ℝ := Real.log 2
  let q : ℝ := min (a - T') (min (1 / K0) (l2 / (L + 1)))
  let δ : ℝ := q / 2
  have hK0 : 0 < K0 := by dsimp [K0]; linarith
  have hl2 : 0 < l2 := Real.log_pos (by norm_num)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hq : 0 < q := by
    dsimp [q]
    exact lt_min (by linarith) (lt_min (by positivity) (by positivity))
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδa : δ < a - T' := by
    have hq' : q ≤ a - T' := min_le_left _ _
    dsimp [δ]
    linarith
  have hδK : δ ≤ 1 / K0 := by
    have hq' : q ≤ 1 / K0 :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    dsimp [δ]
    linarith
  have hδL : L * δ ≤ l2 := by
    have hq' : q ≤ l2 / (L + 1) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hqbound : L * q ≤ l2 := by
      calc
        L * q ≤ L * (l2 / (L + 1)) := mul_le_mul_of_nonneg_left hq' hL
        _ ≤ (L + 1) * (l2 / (L + 1)) := by
          gcongr
          linarith
        _ = l2 := by field_simp
    dsimp [δ]
    nlinarith
  obtain ⟨Cderiv, hCderiv, hShi⟩ :=
    P.local_derivative_estimates m K0 1 (4 * A)
      hK0 (by norm_num) (by positivity)
  refine ⟨Cderiv / δ ^ ((m : ℝ) / 2), by positivity, ?_⟩
  filter_upwards [hAevent, h4event,
    H.eventually_all_time_ball_compact (4 * A) (by positivity)] with k hkA hk4 hkcompact
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
  let : T2Space C.carrier := C.t2Space
  let : SecondCountableTopology C.carrier := C.secondCountable
  change ∀ t ∈ Icc a b, ∀ x ∈ F.ballAt t A,
    (F.flow.connection t).curvatureDerivativeNorm m x ≤ Cderiv / δ ^ ((m : ℝ) / 2)
  intro t ht x hx
  have htI : t ∈ Ioo T' T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hearly : t - δ ∈ Ioo T' T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hshift : (fun u : ℝ ↦ u + (t - δ)) '' Icc 0 δ ⊆ Ioo T' T := by
    rintro _ ⟨u, hu, rfl⟩
    constructor <;> dsimp <;> linarith [hu.1, hu.2, hearly.1, htI.2]
  have hneIcc : (Icc (0 : ℝ) δ).Nontrivial :=
    ⟨0, ⟨le_rfl, hδ.le⟩, δ, ⟨hδ.le, le_rfl⟩, (ne_of_gt hδ).symm⟩
  let Ft := PoincareConjecture.RicciFlow.translate F.flow (t - δ) hshift
    Set.ordConnected_Icc hneIcc
  have hcompact : IsCompact (closure ((Ft.metric 0).ball F.base (4 * A))) := by
    rw [PoincareConjecture.RicciFlow.translate_metric F.flow (t - δ) hshift
      Set.ordConnected_Icc hneIcc 0]
    simpa only [BasedFlow.ballAt, FlowCarrier.metricBall, zero_add] using
      hkcompact (t - δ) hearly
  have hcurv : ∀ u ∈ Icc 0 δ, ∀ y ∈ (Ft.metric 0).ball F.base (4 * A),
      (Ft.connection u).curvatureTensorNorm y ≤ K0 := by
    intro u hu y hy
    have hty : y ∈ F.ballAt (t - δ) (4 * A) := by
      change y ∈ (F.flow.metric (t - δ)).ball F.base (4 * A)
      simpa [Ft, PoincareConjecture.RicciFlow.translate] using hy
    exact le_trans (hk4 (t - δ) hearly (u + (t - δ))
      (hshift ⟨u, hu, rfl⟩) y hty) (by dsimp [K0]; linarith)
  have hderiv := hShi C.carrier δ hδ hδK Ft F.base hcompact hcurv
    δ ⟨hδ, le_rfl⟩
  have hRic : ∀ u ∈ Ioo T' T, ∀ y ∈ F.ballAt t A,
      ∀ v : C.tangent y,
        |(F.flow.connection u).ricci y v v| ≤ L * (F.flow.metric u).inner y v v := by
    intro u hu y hy v
    have hQ : 0 ≤ (F.flow.metric u).inner y v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.flow.metric u).pos y v hv).le
    have hnorm := (F.flow.connection u).abs_ricci_quadratic_le_curvatureTensorNorm y v
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) y) = 3 := finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at hnorm
    exact hnorm.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hkA t htI u hu y hy) (by positivity)) hQ)
  have hball := F.flow.ball_subset_ball_of_ricci_bound (convex_Ioo T' T)
    (Set.Subset.refl _) F.base A L (s := t) (t := t - δ) htI hearly hRic
  have hx2 : x ∈ (F.flow.metric (t - δ)).ball F.base (2 * A) := by
    have hx' := hball hx
    change (F.flow.metric (t - δ)).edist F.base x < ENNReal.ofReal (2 * A)
    have hexp : Real.exp (L * δ) ≤ 2 := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr hδL
    have hrad : Real.exp (L * δ) * A ≤ 2 * A := by nlinarith
    have habs : |t - δ - t| = δ := by
      rw [show t - δ - t = -δ by ring, abs_neg, abs_of_pos hδ]
    rw [habs] at hx'
    exact lt_of_lt_of_le hx' (ENNReal.ofReal_le_ofReal hrad)
  have hx2' : x ∈ (Ft.metric 0).ball F.base (4 * A / 2) := by
    rw [PoincareConjecture.RicciFlow.translate_metric F.flow (t - δ) hshift
      Set.ordConnected_Icc hneIcc 0, zero_add]
    simpa only [show 4 * A / 2 = 2 * A by ring] using hx2
  have h := hderiv x hx2'
  change (F.flow.connection (δ + (t - δ))).curvatureDerivativeNorm m x ≤ _ at h
  rwa [show δ + (t - δ) = t by ring] at h

theorem eventually_two_time_curvatureDerivativeNorm_le_of_m23_predecessors
    {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors)
    (a b : ℝ) (ha : T' < a) (hb : b < T)
    (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
      ∀ s ∈ Ioo T' T, ∀ t ∈ Icc a b, ∀ x ∈ F.ballAt s A,
        (F.flow.connection t).curvatureDerivativeNorm m x ≤ D := by
  obtain ⟨B, hB, hcontain⟩ := H.exists_uniform_ball_containment A hA
  obtain ⟨D, hD, hbound⟩ :=
    H.eventually_interior_curvatureDerivativeNorm_le_of_m23_predecessors
      P a b ha hb B hB m
  refine ⟨D, hD, ?_⟩
  filter_upwards [hcontain, hbound] with k hkcontain hkbound
  dsimp only at hkbound ⊢
  intro s hs t ht x hx
  exact hkbound t ht x (hkcontain s hs t ⟨by linarith [ht.1], by linarith [ht.2]⟩ hx)

theorem eventually_compact_curvatureDerivativeNorm_le_of_m23_predecessors
    {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors)
    {I : Set ℝ} (hIcompact : IsCompact I) (hI : I ⊆ Ioo T' T)
    (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
      ∀ t ∈ I, ∀ x ∈ F.zeroBall A,
        (F.flow.connection t).curvatureDerivativeNorm m x ≤ D := by
  rcases eq_empty_or_nonempty I with rfl | hInonempty
  · refine ⟨1, by norm_num, Filter.Eventually.of_forall ?_⟩
    intro k
    dsimp
    intro t ht
    exact False.elim ht
  obtain ⟨tmin, htmin, hmin⟩ :=
    hIcompact.exists_isMinOn hInonempty continuousOn_id
  obtain ⟨tmax, htmax, hmax⟩ :=
    hIcompact.exists_isMaxOn hInonempty continuousOn_id
  let a : ℝ := (T' + tmin) / 2
  let b : ℝ := (T + tmax) / 2
  have ha : T' < a := by
    dsimp [a]
    linarith [(hI htmin).1, H.time_bounds.1]
  have hb : b < T := by
    dsimp [b]
    linarith [(hI htmax).2, H.time_bounds.2]
  have hIcc : I ⊆ Icc a b := by
    intro t ht
    have hleft : tmin ≤ t := by simpa using hmin ht
    have hright : t ≤ tmax := by simpa using hmax ht
    dsimp [a, b]
    constructor <;> linarith [(hI ht).1, (hI ht).2, (hI htmin).1, (hI htmax).2]
  obtain ⟨D, hD, hbound⟩ :=
    H.eventually_two_time_curvatureDerivativeNorm_le_of_m23_predecessors
      P a b ha hb A hA m
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with k hk
  dsimp only at hk ⊢
  intro t ht x hx
  exact hk 0 ⟨H.time_bounds.1, H.time_bounds.2⟩ t (hIcc ht) x hx

theorem eventually_zero_time_curvatureDerivativeNorm_le_of_m23_predecessors
    {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses 3 T' T)
    (P : M23NormalizedKappaCompactnessPredecessors)
    (A : ℝ) (hA : 0 < A) (m : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ k in Filter.atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
      ∀ x ∈ F.zeroBall A,
        (F.flow.connection 0).curvatureDerivativeNorm m x ≤ D := by
  obtain ⟨D, hD, hbound⟩ :=
    H.eventually_interior_curvatureDerivativeNorm_le_of_m23_predecessors
      P 0 0 H.time_bounds.1 H.time_bounds.2 A hA m
  refine ⟨D, hD, ?_⟩
  filter_upwards [hbound] with k hk
  exact hk 0 ⟨le_rfl, le_rfl⟩

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses

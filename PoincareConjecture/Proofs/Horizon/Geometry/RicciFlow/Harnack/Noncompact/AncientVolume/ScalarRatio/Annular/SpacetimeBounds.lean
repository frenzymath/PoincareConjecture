import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.TimeDerivative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.PullbackCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Gronwall
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter Bundle
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

theorem IsSmoothFamilyOn.contDiffWithinAt_spacetime_pullbackCoefficients
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : ℝ → RiemannianMetric n M} {J : Set ℝ}
    (hg : IsSmoothFamilyOn g J)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) {t : ℝ} (ht : t ∈ J) :
    ContDiffWithinAt ℝ ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (g p.1).pullbackCoefficients f p.2)
      (J ×ˢ univ) (t, x) := by
  have hs := Poincare.Gluing.inducedForm_family_contMDiffWithinAt hg hf ht
  have hc := ((contMDiffWithinAt_hom_bundle _).mp hs).2
  simp only [constant_chart_bilinear_coordinates
    (n := n) (M := EuclideanSpace ℝ (Fin n)) (fun _ _ => rfl)] at hc
  have hid : ContMDiffWithinAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n))
      (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) => (p.1, p.2))
      (J ×ˢ univ) (t, x) :=
    contDiffWithinAt_fst.contMDiffWithinAt.prodMk contDiffWithinAt_snd.contMDiffWithinAt
  convert! (hc.comp (t, x) hid (fun _ hp => hp)).contDiffWithinAt using 1

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.SpacetimeBounds

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem horizon_contDiffOn_spatialFDeriv_within {f : ℝ × V → E} {J : Set ℝ} {U : Set V}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => fderiv ℝ (fun x => f (z.1, x)) z.2)
      (J ×ˢ U) := by
  have hd := (hf.fderivWithin (hJ.prod hU.uniqueDiffOn) (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ V))
  apply hd.congr
  intro z hz
  have hcomp := ((hf z hz).differentiableWithinAt (by simp)).hasFDerivWithinAt.comp z.2
    (((hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)).hasFDerivWithinAt)
    (show MapsTo (fun x : V => (z.1, x)) U (J ×ˢ U) from fun _ hx => ⟨hz.1, hx⟩)
  exact (hcomp.hasFDerivAt (hU.mem_nhds hz.2)).fderiv

theorem contDiffOn_spatialJet_within {f : ℝ × V → E} {J : Set ℝ} {U : Set V}
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ U)) (hJ : UniqueDiffOn ℝ J) (hU : IsOpen U) (m : ℕ) :
    ContDiffOn ℝ ∞ (fun z : ℝ × V => iteratedFDeriv ℝ m (fun x => f (z.1, x)) z.2)
      (J ×ˢ U) := by
  induction m with
  | zero =>
      let e := (continuousMultilinearCurryFin0 ℝ V E).symm.toContinuousLinearEquiv
      exact e.toContinuousLinearMap.contDiff.comp_contDiffOn hf
  | succ m ih =>
      let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => V) E).symm
      convert! e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn
        (horizon_contDiffOn_spatialFDeriv_within ih hJ hU) using 1

end PoincareConjecture.SpacetimeBounds

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem contDiffOn_pullbackCoefficients_within (F : RicciFlow n M J)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (F.metric z.1).pullbackCoefficients e z.2)
      (J ×ˢ U) := by
  intro z hz
  exact (F.smooth.contDiffWithinAt_spacetime_pullbackCoefficients
    (he.contMDiffAt (hU.mem_nhds hz.2)) hz.1).mono (prod_mono subset_rfl (subset_univ _))

theorem differentiableWithinAt_pullbackCoefficients_time (F : RicciFlow n M J)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    DifferentiableWithinAt ℝ (fun s => (F.metric s).pullbackCoefficients e x) J t := by
  have hs := F.contDiffOn_pullbackCoefficients_within hU he (t, x) ⟨ht, hx⟩
  exact (hs.comp t (contDiffWithinAt_id.prodMk contDiffWithinAt_const)
    (show MapsTo (fun s : ℝ => (s, x)) J (J ×ˢ U) from
      fun _ hs => ⟨hs, hx⟩)).differentiableWithinAt (by simp)

theorem derivWithin_pullbackCoefficients_apply (F : RicciFlow n M J)
    (hJ : UniqueDiffOn ℝ J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (u v : EuclideanSpace ℝ (Fin n)) :
    derivWithin (fun s => (F.metric s).pullbackCoefficients e x) J t u v =
      -2 * (F.connection t).ricci (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x u) (mfderiv (𝓡 n) (𝓡 n) e x v) := by
  have hd := F.differentiableWithinAt_pullbackCoefficients_time hU he ht hx
  have hv := (hd.hasDerivWithinAt.clm_apply (hasDerivWithinAt_const t J u)).clm_apply
    (hasDerivWithinAt_const t J v)
  have hv' : HasDerivWithinAt (fun s => (F.metric s).pullbackCoefficients e x u v)
      (derivWithin (fun s => (F.metric s).pullbackCoefficients e x) J t u v) J t := by
    simpa using hv
  exact (hv'.derivWithin (hJ t ht)).symm.trans
    ((F.equation t ht (e x) _ _).derivWithin (hJ t ht))

theorem norm_derivWithin_pullbackCoefficients_le [T2Space M] (F : RicciFlow n M J)
    (hJ : UniqueDiffOn ℝ J) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {b K : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hupper : ∀ v, (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2)
    (hcurv : (F.connection t).curvatureTensorNorm (e x) ≤ K) :
    ‖derivWithin (fun s => (F.metric s).pullbackCoefficients e x) J t‖ ≤
      2 * (n : ℝ) ^ 3 * K * b := by
  have hd := F.differentiableWithinAt_pullbackCoefficients_time hU he ht hx
  have happ (u v : EuclideanSpace ℝ (Fin n)) :
      HasDerivWithinAt (fun s => (F.metric s).pullbackCoefficients e x u v)
        (derivWithin (fun s => (F.metric s).pullbackCoefficients e x) J t u v) J t := by
    simpa using (hd.hasDerivWithinAt.clm_apply (hasDerivWithinAt_const t J u)).clm_apply
      (hasDerivWithinAt_const t J v)
  apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ (by positivity)
  · intro u v
    have heq : (fun s => (F.metric s).pullbackCoefficients e x u v) =
        (fun s => (F.metric s).pullbackCoefficients e x v u) :=
      funext fun s => (F.metric s).symm _ _ _
    have huv := happ u v
    rw [heq] at huv
    exact (huv.derivWithin (hJ t ht)).symm.trans ((happ v u).derivWithin (hJ t ht))
  · intro v
    rw [F.derivWithin_pullbackCoefficients_apply hJ hU he ht hx, abs_mul]
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) (e x)) = n := by
      rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin n)), finrank_euclideanSpace]
      simp
    have hric := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm
      (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
    simp only [Fintype.card_fin, hdim] at hric
    have hnonneg : 0 ≤ (F.metric t).pullbackCoefficients e x v v := by
      let w := mfderiv (𝓡 n) (𝓡 n) e x v
      change 0 ≤ (F.metric t).inner (e x) w w
      by_cases hw : w = 0
      · simp [hw]
      · exact ((F.metric t).pos (e x) w hw).le
    have hbound := hric.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hcurv (by positivity)) (hupper v)
      hnonneg (by positivity))
    calc
      _ ≤ 2 * ((n : ℝ) ^ 3 * K * (b * ‖v‖ ^ 2)) := by
        norm_num only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left hbound (by norm_num)
      _ = _ := by ring

theorem norm_pullbackCoefficients_le_of_ancient_curvature_bound
    [T2Space M] (F : RicciFlow n M (Iic 0))
    (e : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    {a K b : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K) (hb : 0 ≤ b)
    (hcurv : ∀ t ∈ Icc (-a) 0, (F.connection t).curvatureTensorNorm (e x) ≤ K)
    (hzero : ‖(F.metric 0).pullbackCoefficients e x‖ ≤ b)
    {t : ℝ} (ht : t ∈ Icc (-a) 0) :
    ‖(F.metric t).pullbackCoefficients e x‖ ≤ Real.exp (2 * (n : ℝ) ^ 3 * K * a) * b := by
  have hnonneg (s : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
      0 ≤ (F.metric s).pullbackCoefficients e x v v := by
    let w := mfderiv (𝓡 n) (𝓡 n) e x v
    change 0 ≤ (F.metric s).inner (e x) w w
    by_cases hw : w = 0
    · simp [hw]
    · exact ((F.metric s).pos (e x) w hw).le
  apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ (by positivity)
  · exact fun v w => (F.metric t).symm _ _ _
  · intro v
    rw [abs_of_nonneg (hnonneg t v)]
    have hRic : ∀ s ∈ Icc (-a) 0,
        |(F.connection s).ricci (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
          (mfderiv (𝓡 n) (𝓡 n) e x v)| ≤
        ((n : ℝ) ^ 3 * K) * (F.metric s).inner (e x)
          (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x v) := by
      intro s hs
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) (e x)) = n :=
        finrank_euclideanSpace_fin
      have h := (F.connection s).abs_ricci_quadratic_le_curvatureTensorNorm
        (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
      simp only [Fintype.card_fin, hdim] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcurv s hs) (by positivity)) (hnonneg s v))
    have hcomp := (F.metric_inner_self_exp_bounds (convex_Icc (-a) 0)
      (fun _ hs => hs.2) (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
      ((n : ℝ) ^ 3 * K) hRic (show (0 : ℝ) ∈ Icc (-a) 0 by constructor <;> linarith) ht).2
    change (F.metric t).pullbackCoefficients e x v v ≤
      Real.exp (2 * ((n : ℝ) ^ 3 * K) * |t - 0|) *
        (F.metric 0).pullbackCoefficients e x v v at hcomp
    have habs : |t - 0| ≤ a := by rw [sub_zero, abs_of_nonpos ht.2]; linarith [ht.1]
    have hexp : Real.exp (2 * ((n : ℝ) ^ 3 * K) * |t - 0|) ≤
        Real.exp (2 * (n : ℝ) ^ 3 * K * a) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left habs (show 0 ≤ 2 * ((n : ℝ) ^ 3 * K) by positivity)]
    have hinit : (F.metric 0).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2 := by
      have h := ((F.metric 0).pullbackCoefficients e x).le_opNorm₂ v v
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg 0 v)] at h
      calc
        _ ≤ ‖(F.metric 0).pullbackCoefficients e x‖ * ‖v‖ * ‖v‖ := h
        _ ≤ b * ‖v‖ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hzero (sq_nonneg ‖v‖)]
    exact hcomp.trans ((mul_le_mul hexp hinit (hnonneg 0 v) (Real.exp_nonneg _)).trans_eq
      (by ring))

theorem exists_ancient_exponential_coefficient_time_bounds
    (hC : RicciFlowCurvatureTheory.{u}) (n : ℕ) {K S ρ a : ℝ}
    (hK : 0 < K) (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S / 2) (ha : 0 ≤ a) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (F : RicciFlow n M (Iic 0)),
        (∀ t ≤ 0, MetricComplete (F.metric t)) →
        (∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
        (∀ t ≤ 0, ∀ x ∈ (F.metric 0).ball p (2 * S),
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
          Φ.source = Metric.ball 0 S → Φ 0 = p →
          (∀ v w, (F.metric 0).pullbackCoefficients (extChartAt (𝓡 n) p).symm
            (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) →
          HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w)) L.toContinuousLinearMap 0 →
          (∀ w ∈ Metric.ball 0 S,
            (F.metric 0).IsGeodesicOn (fun t => Φ (t • w))
              {t : ℝ | t • w ∈ Metric.ball 0 S}) →
          (∀ w ∈ Metric.ball 0 S,
            (F.metric 0).edist p (Φ w) = ENNReal.ofReal ‖w‖) →
          ∀ t ∈ Icc (-a) 0, ∀ x ∈ Metric.closedBall 0 ρ,
            ‖(F.metric t).pullbackCoefficients Φ x‖ ≤ B ∧
            ‖derivWithin (fun s => (F.metric s).pullbackCoefficients Φ x) (Iic 0) t‖ ≤ B := by
  obtain ⟨Z, hZ, hterminal⟩ :=
    exists_terminal_exponential_metric_jet_bound hC n 0 hK hS hρ hρS
  let b : ℝ := Real.exp (2 * (n : ℝ) ^ 3 * K * a) * Z
  have hb : 0 ≤ b := mul_nonneg (Real.exp_nonneg _) hZ
  refine ⟨max b (2 * (n : ℝ) ^ 3 * K * b), le_max_of_le_left hb, ?_⟩
  intro M _ _ _ _ _ _ F hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist
    t ht x hx
  have hxnorm : ‖x‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hxS : x ∈ Metric.ball 0 S := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hxball : Φ x ∈ (F.metric 0).ball p (2 * S) := by
    change (F.metric 0).edist p (Φ x) < ENNReal.ofReal (2 * S)
    rw [hdist x hxS, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)]
    linarith
  have hz : ‖(F.metric 0).pullbackCoefficients Φ x‖ ≤ Z := by
    simpa only [norm_iteratedFDeriv_zero] using hterminal M F hcomplete hoperator p hcurv
      L Φ hsource hzero hL hderiv hgeo hdist x hx
  have hnorm : ‖(F.metric t).pullbackCoefficients Φ x‖ ≤ b :=
    F.norm_pullbackCoefficients_le_of_ancient_curvature_bound Φ x ha hK.le hZ
      (fun s hs => hcurv s hs.2 (Φ x) hxball) hz ht
  refine ⟨hnorm.trans (le_max_left _ _), ?_⟩
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Φ (Metric.ball 0 S) := by
    simpa only [hsource] using Φ.contMDiffOn
  have hupper (v : EuclideanSpace ℝ (Fin n)) :
      (F.metric t).pullbackCoefficients Φ x v v ≤ b * ‖v‖ ^ 2 := by
    have h := ((F.metric t).pullbackCoefficients Φ x).le_opNorm₂ v v
    have habs := le_abs_self ((F.metric t).pullbackCoefficients Φ x v v)
    rw [← Real.norm_eq_abs] at habs
    exact (habs.trans h).trans (by
      nlinarith [mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖v‖)])
  exact (F.norm_derivWithin_pullbackCoefficients_le (uniqueDiffOn_Iic 0)
    Metric.isOpen_ball he ht.2 hxS hb hK.le hupper (hcurv t ht.2 (Φ x) hxball)).trans
      (le_max_right _ _)

theorem exists_ancient_terminal_ball_curvatureDerivative_bound
    (hC : RicciFlowCurvatureTheory.{u}) (n k : ℕ) {K R : ℝ}
    (hK : 0 < K) (hR : 0 < R) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (F : RicciFlow n M (Iic 0)),
        (∀ t ≤ 0, MetricComplete (F.metric t)) →
        (∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
        (∀ t ≤ 0, ∀ x ∈ (F.metric 0).ball p R,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ t ≤ 0, ∀ x ∈ (F.metric 0).ball p (R / 2),
          (F.connection t).curvatureDerivativeNorm k x ≤ D := by
  obtain ⟨D, hD, hbound⟩ := exists_terminal_ball_curvatureDerivative_bound hC n k hK
    (by positivity : 0 < R / 2)
  refine ⟨D, hD, ?_⟩
  intro M _ _ _ _ _ _ F hcomplete hoperator p hcurv t ht x hx
  have hshift : (fun s : ℝ => s + t) '' Iic 0 ⊆ Iic 0 := by
    rintro _ ⟨s, hs, rfl⟩
    exact add_nonpos hs ht
  have hne : (Iic (0 : ℝ)).Nontrivial :=
    ⟨-1, by norm_num, 0, by simp, by norm_num⟩
  let Ft := F.translate t hshift ordConnected_Iic hne
  have hcomplete' : ∀ s ≤ 0, MetricComplete (Ft.metric s) :=
    fun s hs => hcomplete (s + t) (add_nonpos hs ht)
  have hoperator' : ∀ s ≤ 0, ∀ y, (Ft.connection s).NonnegativeCurvatureOperator y :=
    fun s hs y => hoperator (s + t) (add_nonpos hs ht) y
  have hball : (Ft.metric 0).ball x (R / 2) ⊆ (F.metric 0).ball x (R / 2) := by
    change (F.metric (0 + t)).ball x (R / 2) ⊆ _
    rw [zero_add]
    exact F.ball_subset_terminal_ball_of_ancient_ricci_nonneg x (R / 2) ht
      (fun s hs y _ v => ((F.connection s).ricci_bounds_of_nonnegative_curvatureOperator
        (hC.tensor_calculus n M (F.metric s) (F.connection s)) y
          (hoperator s hs y) v).1)
  have hcurv' : ∀ s ≤ 0, ∀ y ∈ (Ft.metric 0).ball x (R / 2),
      (Ft.connection s).curvatureTensorNorm y ≤ K := by
    intro s hs y hy
    apply hcurv (s + t) (add_nonpos hs ht) y
    have hy' := hball hy
    let := (F.metric 0).toMetricSpace
    rw [← (F.metric 0).toMetricSpace_ball] at hx hy' ⊢
    exact Metric.ball_subset_ball' (by
      have hx' : dist x p < R / 2 := hx
      linarith) hy'
  have hxcenter : x ∈ (Ft.metric 0).ball x (R / 2 / 4) := by
    let := (Ft.metric 0).toMetricSpace
    rw [← (Ft.metric 0).toMetricSpace_ball]
    exact Metric.mem_ball_self (by positivity)
  have h := hbound M Ft hcomplete' hoperator' x hcurv' x hxcenter
  change (F.connection (0 + t)).curvatureDerivativeNorm k x ≤ D at h
  rwa [zero_add] at h

theorem exists_ancient_exponential_ellipticity_radius
    (hC : RicciFlowCurvatureTheory.{u}) (n : ℕ) {K S : ℝ} (hK : 0 < K) (hS : 0 < S) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < S / 2 ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [SecondCountableTopology M] [ConnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (F : RicciFlow n M (Iic 0)),
        (∀ t ≤ 0, MetricComplete (F.metric t)) →
        (∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M,
        (∀ t ≤ 0, ∀ x ∈ (F.metric 0).ball p (2 * S),
          (F.connection t).curvatureTensorNorm x ≤ K) →
        ∀ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
          Φ.source = Metric.ball 0 S → Φ 0 = p →
          (∀ v w, (F.metric 0).pullbackCoefficients (extChartAt (𝓡 n) p).symm
            (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) →
          HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w)) L.toContinuousLinearMap 0 →
          (∀ w ∈ Metric.ball 0 S,
            (F.metric 0).IsGeodesicOn (fun t => Φ (t • w))
              {t : ℝ | t • w ∈ Metric.ball 0 S}) →
          (∀ w ∈ Metric.ball 0 S,
            (F.metric 0).edist p (Φ w) = ENNReal.ofReal ‖w‖) →
          ∀ t ≤ 0, ∀ x ∈ Metric.closedBall 0 ρ, ∀ v,
            (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients Φ x v v := by
  obtain ⟨Z, hZ, hjet⟩ := exists_terminal_exponential_metric_jet_bound hC n 1 hK hS
    (ρ := S / 4) (by positivity) (by linarith)
  let ρ : ℝ := min (S / 8) (1 / (2 * (Z + 1)))
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρS : ρ < S / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρquarter : ρ ≤ S / 4 := (min_le_left _ _).trans (by linarith)
  have hZρ : Z * ρ ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (Z + 1))).mp
      (show ρ ≤ 1 / (2 * (Z + 1)) from min_le_right _ _)
    nlinarith
  refine ⟨ρ, hρ, hρS, ?_⟩
  intro M _ _ _ _ _ _ F hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist
    t ht x hx v
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Φ (Metric.ball 0 S) := by
    simpa only [hsource] using Φ.contMDiffOn
  let B := (F.metric 0).pullbackCoefficients Φ
  have hnorm := (F.metric 0).pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hS)))
    hzero hderiv hL
  have hsmall : ‖B x - B 0‖ ≤ 1 / 2 := by
    have hxquarter : x ∈ Metric.closedBall 0 (S / 4) :=
      Metric.closedBall_subset_closedBall hρquarter hx
    have hmean := (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) (S / 4)).norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => ((F.metric 0).contDiffAt_pullbackCoefficients
        (he.contMDiffAt (Metric.isOpen_ball.mem_nhds
          (Metric.closedBall_subset_ball (by linarith : S / 4 < S) hy)))).differentiableAt (by simp))
      (fun y hy => by
        simpa only [norm_iteratedFDeriv_one] using hjet M F hcomplete hoperator p hcurv
          L Φ hsource hzero hL hderiv hgeo hdist y hy)
      (Metric.mem_closedBall_self (by positivity : 0 ≤ S / 4)) hxquarter
    have hxnorm : ‖x‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    rw [sub_zero] at hmean
    exact hmean.trans ((mul_le_mul_of_nonneg_left hxnorm hZ).trans hZρ)
  have hbilinear := (B x - B 0).le_opNorm₂ v v
  have habs : |B x v v - ‖v‖ ^ 2| ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := by
    have h : ‖(B x - B 0) v v‖ ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 := hbilinear.trans (by
      nlinarith [mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖v‖)])
    simpa only [sub_apply, B, hnorm, real_inner_self_eq_norm_sq, Real.norm_eq_abs] using h
  have hlower : (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ B x v v := by
    have h := (abs_le.mp habs).1
    linarith
  apply hlower.trans
  exact F.antitoneOn_metric_inner_self_on_ancient_of_ricci_nonneg (Φ x)
    (mfderiv (𝓡 n) (𝓡 n) Φ x v)
    (fun s hs => ((F.connection s).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M (F.metric s) (F.connection s)) (Φ x)
        (hoperator s hs (Φ x)) (mfderiv (𝓡 n) (𝓡 n) Φ x v)).1) ht (by simp) ht

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.SpacetimeBounds

theorem exists_ancient_chart_spatial_jet_bound
    (n m : ℕ) (K Z : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a α b : ℝ} (hα : 0 < α) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (F : RicciFlow n M (Iic 0))
        {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible) →
        ∀ W : Set (EuclideanSpace ℝ (Fin n)), W ⊆ U →
        (∀ t ∈ Icc (-a) 0, ∀ x ∈ W, ∀ v,
          α * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v ∧
          (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ j t, t ∈ Icc (-a) 0 → ∀ x ∈ W,
          (F.connection t).curvatureDerivativeNorm j (e x) ≤ K j) →
        (∀ j x, x ∈ W → ‖iteratedFDeriv ℝ j ((F.metric 0).pullbackCoefficients e) x‖ ≤ Z j) →
        ∀ t ∈ Icc (-a) 0, ∀ x ∈ W, ∀ j ≤ m,
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B := by
  induction m with
  | zero =>
      refine ⟨b, hb, ?_⟩
      intro M _ _ _ F U hU e he hi W hWU hell hcurv hterminal t ht x hx j hj
      have hj0 : j = 0 := by omega
      subst j
      rw [norm_iteratedFDeriv_zero]
      apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
      · exact fun v w => (F.metric t).symm _ _ _
      · intro v
        rw [abs_of_nonneg (le_trans (by positivity) (hell t ht x hx v).1)]
        exact (hell t ht x hx v).2
  | succ q ih =>
      obtain ⟨B, hB, hprevious⟩ := ih
      let A : ℝ := max B 1
      have hA : 1 ≤ A := le_max_right _ _
      obtain ⟨C, hC, hevol⟩ := exists_affine_spatialJet_evolution_bound n q K hK hα hb A hA
      let E : ℝ := max (Z (q + 1)) 1 * Real.exp ((C + C) * a)
      have hE : 0 ≤ E := by dsimp only [E]; positivity
      refine ⟨max B E, le_max_of_le_left hB, ?_⟩
      intro M _ _ _ F U hU e he hi W hWU hell hcurv hterminal t ht x hx j hj
      have hlower := hprevious F hU he hi W hWU hell hcurv hterminal
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · apply le_trans _ (le_max_right B E)
        let Fneg := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
          (show Iio (0 : ℝ) ⊆ Iic 0 from fun s hs =>
            show s ≤ 0 from le_of_lt hs) ordConnected_Iio
          (show (Iio (0 : ℝ)).Nontrivial from
            ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩)
        have hjoint : ContDiffOn ℝ ∞
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              iteratedFDeriv ℝ (q + 1) ((F.metric z.1).pullbackCoefficients e) z.2)
            (Iic 0 ×ˢ U) := contDiffOn_spatialJet_within
          (F.contDiffOn_pullbackCoefficients_within hU he) (uniqueDiffOn_Iic 0) hU (q + 1)
        have hcont : ContinuousOn
            (fun s => iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x)
            (Icc (-a) 0) := by
          have htime : Continuous (fun u : ℝ => (u, x)) :=
            continuous_id.prodMk continuous_const
          exact hjoint.continuousOn.comp (f := fun u : ℝ => (u, x)) htime.continuousOn
            (show MapsTo (fun u : ℝ => (u, x)) (Icc (-a) 0) (Iic 0 ×ˢ U) from
              fun _ hu => ⟨hu.2, hWU hx⟩)
        have hdiff : ∀ s ∈ Ioo (-a) 0, DifferentiableAt ℝ
            (fun u => iteratedFDeriv ℝ (q + 1) ((F.metric u).pullbackCoefficients e) x) s := by
          intro s hs
          have hsm := contDiffOn_spatialJet
            (Fneg.contDiffOn_pullbackCoefficients isOpen_Iio hU he) isOpen_Iio hU (q + 1)
          exact ((hsm.contDiffAt (x := (s, x))
            ((isOpen_Iio.prod hU).mem_nhds ⟨hs.2, hWU hx⟩)).comp s
            (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
        have hbound : ∀ s ∈ Ioo (-a) 0,
            ‖deriv (fun u => iteratedFDeriv ℝ (q + 1)
              ((F.metric u).pullbackCoefficients e) x) s‖ ≤
            C + C * ‖iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x‖ := by
          intro s hs
          have hsclosed : s ∈ Icc (-a) 0 := ⟨hs.1.le, hs.2.le⟩
          have h := hevol Fneg isOpen_Iio hU he hi hs.2 (hWU hx)
            (fun v => (hell s hsclosed x hx v).1) (fun v => (hell s hsclosed x hx v).2)
            (fun d _ => hcurv d s hsclosed x hx)
            (fun d hd hdq => (hlower s hsclosed x hx d hdq).trans
              ((le_max_left B 1).trans (by
                simpa only [pow_one] using pow_le_pow_right₀ hA hd)))
          simpa only [Fneg, Poincare.Geometry.RicciFlow.Harnack.restrictFlow, mul_add, mul_one] using h
        have hprop := norm_le_exp_of_affine_deriv_bound_Icc hcont hdiff hC hC
          (hterminal (q + 1) x hx) hbound ht
        apply hprop.trans
        apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) (le_max_right (Z (q + 1)) 1))
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (add_nonneg hC hC)
        rw [abs_of_nonpos ht.2]
        linarith [ht.1]
      · exact (hlower t ht x hx j (by omega)).trans (le_max_left B E)

end PoincareConjecture.SpacetimeBounds

namespace PoincareConjecture.RicciFlow

theorem exists_ancient_exponential_spatial_jet_bounds
    (hC : RicciFlowCurvatureTheory.{u}) (n : ℕ) {K S : ℝ} (hK : 0 < K) (hS : 0 < S) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < S / 2 ∧ ∀ a : ℝ, 0 ≤ a → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
          [SecondCountableTopology M] [ConnectedSpace M]
          [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
          (F : RicciFlow n M (Iic 0)),
          (∀ t ≤ 0, MetricComplete (F.metric t)) →
          (∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x) →
          ∀ p : M,
          (∀ t ≤ 0, ∀ x ∈ (F.metric 0).ball p (2 * S),
            (F.connection t).curvatureTensorNorm x ≤ K) →
          ∀ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
          ∀ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
            Φ.source = Metric.ball 0 S → Φ 0 = p →
            (∀ v w, (F.metric 0).pullbackCoefficients (extChartAt (𝓡 n) p).symm
              (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) →
            HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w)) L.toContinuousLinearMap 0 →
            (∀ w ∈ Metric.ball 0 S,
              (F.metric 0).IsGeodesicOn (fun t => Φ (t • w))
                {t : ℝ | t • w ∈ Metric.ball 0 S}) →
            (∀ w ∈ Metric.ball 0 S,
              (F.metric 0).edist p (Φ w) = ENNReal.ofReal ‖w‖) →
            ∀ t ∈ Icc (-a) 0, ∀ x ∈ Metric.closedBall 0 ρ, ∀ j ≤ m,
              ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients Φ) x‖ ≤ B := by
  obtain ⟨ρ, hρ, hρS, helliptic⟩ := exists_ancient_exponential_ellipticity_radius hC n hK hS
  refine ⟨ρ, hρ, hρS, ?_⟩
  intro a ha m
  choose D hD hcurvature using fun j =>
    exists_ancient_terminal_ball_curvatureDerivative_bound hC n j hK (by positivity : 0 < 2 * S)
  choose Z _hZ hterminal using fun j =>
    exists_terminal_exponential_metric_jet_bound hC n j hK hS hρ hρS
  obtain ⟨b, hb, hcoefficient⟩ :=
    exists_ancient_exponential_coefficient_time_bounds hC n hK hS hρ hρS ha
  obtain ⟨B, hB, hprop⟩ := SpacetimeBounds.exists_ancient_chart_spatial_jet_bound
    n m D Z (fun j => (hD j).le) (a := a) (α := 1 / 2) (by norm_num) hb
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ _ _ F hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Φ (Metric.ball 0 S) := by
    simpa only [hsource] using Φ.contMDiffOn
  have hi : ∀ x ∈ Metric.ball 0 S, (mfderiv (𝓡 n) (𝓡 n) Φ x).IsInvertible := by
    intro x hx
    exact ⟨(Φ.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      (hsource.symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ Metric.ball 0 S :=
    Metric.closedBall_subset_ball (by linarith)
  apply hprop F Metric.isOpen_ball he hi (Metric.closedBall 0 ρ) hsub
  · intro t ht x hx v
    refine ⟨helliptic M F hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist
      t ht.2 x hx v, ?_⟩
    have hnorm := (hcoefficient M F hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv
      hgeo hdist t ht x hx).1
    have h := ((F.metric t).pullbackCoefficients Φ x).le_opNorm₂ v v
    have habs := le_abs_self ((F.metric t).pullbackCoefficients Φ x v v)
    rw [← Real.norm_eq_abs] at habs
    exact (habs.trans h).trans (by
      nlinarith [mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖v‖)])
  · intro j t ht x hx
    apply hcurvature j M F hcomplete hoperator p hcurv t ht.2 (Φ x)
    change (F.metric 0).edist p (Φ x) < ENNReal.ofReal (2 * S / 2)
    rw [hdist x (hsub hx), ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg x)]
    have hxnorm : ‖x‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    linarith
  · intro j x hx
    exact hterminal j M F hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist x hx

theorem exists_ancient_exponential_spacetime_jet_bounds
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {K S : ℝ} (hK : 0 < K) (hS : 0 < S)
    (F : ℕ → RicciFlow n M (Iic 0))
    (hcomplete : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hoperator : ∀ k t, t ≤ 0 → ∀ x,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (p : ℕ → M)
    (hcurv : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (2 * S),
      ((F k).connection t).curvatureTensorNorm x ≤ K)
    (L : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (hzero : ∀ k, Φ k 0 = p k)
    (hL : ∀ k v w, ((F k).metric 0).pullbackCoefficients
      (extChartAt (𝓡 n) (p k)).symm (extChartAt (𝓡 n) (p k) (p k))
        (L k v) (L k w) = inner ℝ v w)
    (hderiv : ∀ k, HasFDerivAt (fun w => extChartAt (𝓡 n) (p k) (Φ k w))
      (L k).toContinuousLinearMap 0)
    (hgeo : ∀ k w, w ∈ Metric.ball 0 S →
      ((F k).metric 0).IsGeodesicOn (fun t => Φ k (t • w))
        {t : ℝ | t • w ∈ Metric.ball 0 S})
    (hdist : ∀ k w, w ∈ Metric.ball 0 S →
      ((F k).metric 0).edist (p k) (Φ k w) = ENNReal.ofReal ‖w‖) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < S / 2 ∧ ∀ a : ℝ, 0 < a → ∀ m : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ k, ∀ t ∈ Ioo (-a) 0, ∀ x ∈ Metric.closedBall 0 ρ,
        ‖iteratedFDeriv ℝ m (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
          ((F k).metric z.1).pullbackCoefficients (Φ k) z.2) (t, x)‖ ≤ B := by
  classical
  obtain ⟨ρs, hρs, hρsS, hspatial⟩ := exists_ancient_exponential_spatial_jet_bounds hC n hK hS
  obtain ⟨ρe, hρe, _, helliptic⟩ := exists_ancient_exponential_ellipticity_radius hC n hK hS
  let ρ : ℝ := min ρs ρe
  have hρ : 0 < ρ := lt_min hρs hρe
  have hρS : ρ < S / 2 := lt_of_le_of_lt (min_le_left _ _) hρsS
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ ⊆ Metric.ball 0 S :=
    Metric.closedBall_subset_ball (by linarith)
  refine ⟨ρ, hρ, hρS, ?_⟩
  intro a ha m
  let f : ℕ → ℝ × EuclideanSpace ℝ (Fin n) → SpacetimeBounds.MetricCoefficient n :=
    fun k z => ((F k).metric z.1).pullbackCoefficients (Φ k) z.2
  let W : ℕ → Set (ℝ × EuclideanSpace ℝ (Fin n)) :=
    fun _ => Ioo (-a) 0 ×ˢ Metric.closedBall 0 ρ
  let Fneg (k : ℕ) := Poincare.Geometry.RicciFlow.Harnack.restrictFlow (F k)
    (show Iio (0 : ℝ) ⊆ Iic 0 from fun s hs => show s ≤ 0 from le_of_lt hs) ordConnected_Iio
    (show (Iio (0 : ℝ)).Nontrivial from ⟨-2, by norm_num, -1, by norm_num, by norm_num⟩)
  have he (k : ℕ) : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Φ k) (Metric.ball 0 S) := by
    simpa only [hsource k] using (Φ k).contMDiffOn
  have hi (k : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 S) :
      (mfderiv (𝓡 n) (𝓡 n) (Φ k) x).IsInvertible :=
    ⟨((Φ k).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      ((hsource k).symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  have hf (k : ℕ) : ContDiffOn ℝ ∞ (f k) (Iio 0 ×ˢ Metric.ball 0 S) :=
    (Fneg k).contDiffOn_pullbackCoefficients isOpen_Iio Metric.isOpen_ball (he k)
  have hrange (k : ℕ) (z : ℝ × EuclideanSpace ℝ (Fin n))
      (hz : z ∈ Iio 0 ×ˢ Metric.ball 0 S) :
      SpacetimeBounds.Bootstrap.spatialJet 2 (f k) z ∈ SpacetimeBounds.jetRicciFlowDomain n := by
    change ((SpacetimeBounds.twoJetProjection n
      (SpacetimeBounds.Bootstrap.spatialJet 2 (f k) z)).1).IsInvertible
    rw [SpacetimeBounds.twoJetProjection_spatialJet]
    exact ((F k).metric z.1).isInvertible_pullbackCoefficients (hi k z.2 hz.2).injective
  have hevol (k : ℕ) (z : ℝ × EuclideanSpace ℝ (Fin n))
      (hz : z ∈ Iio 0 ×ˢ Metric.ball 0 S) :
      deriv (fun t => f k (t, z.2)) z.1 =
        SpacetimeBounds.jetRicciFlowOperator n (SpacetimeBounds.Bootstrap.spatialJet 2 (f k) z) := by
    rw [SpacetimeBounds.jetRicciFlowOperator, Function.comp_apply,
      SpacetimeBounds.twoJetProjection_spatialJet]
    exact SpacetimeBounds.deriv_pullbackCoefficients_eq_ricciFlowOperator (Fneg k)
      isOpen_Iio Metric.isOpen_ball (he k) (hi k) hz.1 hz.2
  have hall (q : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ k, ∀ z ∈ W k, ∀ j ≤ q,
      ‖iteratedFDeriv ℝ j (fun x => f k (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hbound⟩ := hspatial a ha.le q
    refine ⟨B, hB, ?_⟩
    intro k z hz j hj
    exact hbound M (F k) (hcomplete k) (hoperator k) (p k) (hcurv k) (L k) (Φ k)
      (hsource k) (hzero k) (hL k) (hderiv k) (hgeo k) (hdist k)
      z.1 ⟨hz.1.1.le, hz.1.2.le⟩ z.2
      (Metric.closedBall_subset_closedBall (min_le_left _ _) hz.2) j hj
  have hspatial' (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in (⊤ : Filter ℕ), ∀ z ∈ W k,
      ‖iteratedFDeriv ℝ j (fun x => f k (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ := hall j
    exact ⟨B, hB, Filter.Eventually.of_forall (fun k z hz => hb k z hz j le_rfl)⟩
  have hcompact (j : ℕ) : ∃ Q : Set (SpacetimeBounds.Bootstrap.Jet
      (EuclideanSpace ℝ (Fin n)) (SpacetimeBounds.MetricCoefficient n) (2 + j)),
      IsCompact Q ∧ Q ⊆ (SpacetimeBounds.Bootstrap.baseProjection 2 j) ⁻¹'
        SpacetimeBounds.jetRicciFlowDomain n ∧
      ∀ᶠ k in (⊤ : Filter ℕ), MapsTo (SpacetimeBounds.Bootstrap.spatialJet (2 + j) (f k)) (W k) Q := by
    obtain ⟨B, hB, hb⟩ := hall (2 + j)
    obtain ⟨Q, hQ, hQdomain, hbox⟩ :=
      SpacetimeBounds.exists_compact_elliptic_jet_box n j (a := 1 / 2) (by norm_num) B
    refine ⟨Q, hQ, hQdomain, Filter.Eventually.of_forall ?_⟩
    intro k z hz
    apply hbox
    · exact (pi_norm_le_iff_of_nonneg hB).mpr (fun d => hb k z hz d (by omega))
    · intro v
      exact helliptic M (F k) (hcomplete k) (hoperator k) (p k) (hcurv k) (L k) (Φ k)
        (hsource k) (hzero k) (hL k) (hderiv k) (hgeo k) (hdist k)
        z.1 hz.1.2.le z.2 (Metric.closedBall_subset_closedBall (min_le_right _ _) hz.2) v
  obtain ⟨B, hB, hbound⟩ := SpacetimeBounds.Bootstrap.eventuallyBounded_spacetime_jets
    (⊤ : Filter ℕ) (SpacetimeBounds.isOpen_jetRicciFlowDomain n)
    (SpacetimeBounds.contDiffOn_jetRicciFlowOperator n) f
    (fun _ => Iio 0) (fun _ => Metric.ball 0 S) W hf
    (fun _ => isOpen_Iio) (fun _ => Metric.isOpen_ball)
    (fun _ _ hz => ⟨hz.1.2, hsub hz.2⟩) hrange hevol hspatial' hcompact m
  refine ⟨B, hB, ?_⟩
  intro k t ht x hx
  exact (Filter.eventually_top.mp hbound) k (t, x) ⟨ht, hx⟩

end PoincareConjecture.RicciFlow

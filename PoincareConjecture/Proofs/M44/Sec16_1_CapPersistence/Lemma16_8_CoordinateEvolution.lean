import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_ClosedTimeJets
import PoincareConjecture.Proofs.M44.Mathlib.ClosedTimeGronwall
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialEvolution










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




def closedSlabInterior {a b : ℝ} (hab : a < b) (F : RicciFlow n M (Icc a b)) :
    RicciFlow n M (Ioo a b) where
  metric := F.metric
  connection := F.connection
  interval := ordConnected_Ioo
  nontrivial := by
    obtain ⟨c, hac, hcb⟩ := exists_between hab
    obtain ⟨d, hcd, hdb⟩ := exists_between hcb
    exact ⟨c, ⟨hac, hcb⟩, d, ⟨hac.trans hcd, hdb⟩, hcd.ne⟩
  smooth := F.smooth.mono (prod_mono Ioo_subset_Icc_self (Subset.refl _))
  equation t ht x v w := (F.equation t (Ioo_subset_Icc_self ht) x v w).mono Ioo_subset_Icc_self

private theorem norm_deriv_zeroth_jet
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → V → E) (x : V) {t : ℝ} (hf : DifferentiableAt ℝ (fun s => f s x) t) :
    ‖deriv (fun s => iteratedFDeriv ℝ 0 (f s) x) t‖ = ‖deriv (fun s => f s x) t‖ := by
  let c := (continuousMultilinearCurryFin0 ℝ V E).symm
  have hd : HasDerivAt (fun s => iteratedFDeriv ℝ 0 (f s) x)
      (c (deriv (fun s => f s x) t)) t :=
    c.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf.hasDerivAt
  rw [hd.deriv, c.norm_map]




theorem closed_metric_zeroth_jet_estimates [T2Space M]
    {l r b K : ℝ} (hlr : l < r) (hb : 0 ≤ b) (hK : 0 ≤ K)
    (F : RicciFlow n M (Icc l r)) {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hupper : ∀ t ∈ Icc l r, ∀ x ∈ U, ∀ v,
      (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2)
    (hcurv : ∀ t ∈ Icc l r, ∀ x ∈ U, (F.connection t).curvatureTensorNorm (e x) ≤ K) :
    ∀ x ∈ U,
      (∀ t ∈ Icc l r, ‖iteratedFDeriv ℝ 0 ((F.metric t).pullbackCoefficients e) x‖ ≤ b) ∧
      (∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
        ‖iteratedFDeriv ℝ 0 ((F.metric t).pullbackCoefficients e) x -
          iteratedFDeriv ℝ 0 ((F.metric s).pullbackCoefficients e) x‖ ≤
            (2 * (n : ℝ) ^ 3 * K * b) * |t - s|) := by
  intro x hx
  constructor
  · intro t ht
    rw [norm_iteratedFDeriv_zero]
    apply HarmonicCoordinates.norm_bilinear_le_of_quadratic _ hb
    · exact fun v w => (F.metric t).symm _ _ _
    · intro v
      have hnonneg : 0 ≤ (F.metric t).pullbackCoefficients e x v v := by
        let w := mfderiv (𝓡 n) (𝓡 n) e x v
        change 0 ≤ (F.metric t).inner (e x) w w
        by_cases hw : w = 0
        · simp only [hw, map_zero]
          exact le_rfl
        · exact ((F.metric t).pos _ _ hw).le
      rw [abs_of_nonneg hnonneg]
      exact hupper t ht x hx v
  · apply norm_sub_le_of_interior_deriv_bound hlr
      ((contDiffOn_pullback_spatialJet_time hlr F hU he 0 hx).of_le (by simp))
    intro t ht
    let G := closedSlabInterior hlr F
    rw [norm_deriv_zeroth_jet _ x
      (G.differentiableAt_pullbackCoefficients_time isOpen_Ioo hU he ht hx)]
    exact G.norm_deriv_pullbackCoefficients_le isOpen_Ioo hU he ht hx hb hK
      (hupper t (Ioo_subset_Icc_self ht) x hx) (hcurv t (Ioo_subset_Icc_self ht) x hx)




theorem exists_closed_spatial_succ_estimates
    (n q : ℕ) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b A Z T : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hA : 1 ≤ A)
    (hZ : 1 ≤ Z) (hT : 0 ≤ T) :
    ∃ B L : ℝ, 1 ≤ B ∧ 0 ≤ L ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {l r : ℝ} (_hlr : l < r) (F : RicciFlow n M (Icc l r)), r - l ≤ T →
        ∀ {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        (∀ t ∈ Icc l r, ∀ x ∈ U, ∀ v,
          a * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v) →
        (∀ t ∈ Icc l r, ∀ x ∈ U, ∀ v,
          (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ t ∈ Icc l r, ∀ x ∈ U, ∀ s ≤ q + 1,
          (F.connection t).curvatureDerivativeNorm s (e x) ≤ K s) →
        (∀ t ∈ Icc l r, ∀ x ∈ U, ∀ j, 1 ≤ j → j ≤ q →
          ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ A) →
        (∀ x ∈ U, ‖iteratedFDeriv ℝ (q + 1) ((F.metric l).pullbackCoefficients e) x‖ ≤ Z) →
        ∀ x ∈ U,
          (∀ t ∈ Icc l r,
            ‖iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients e) x‖ ≤ B) ∧
          (∀ s ∈ Icc l r, ∀ t ∈ Icc l r,
            ‖iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients e) x -
              iteratedFDeriv ℝ (q + 1) ((F.metric s).pullbackCoefficients e) x‖ ≤ L * |t - s|) := by
  obtain ⟨C, hC, hevol⟩ := SpacetimeBounds.exists_affine_spatialJet_evolution_bound
    n q K hK ha hb A hA
  let B := Z * Real.exp ((2 * C) * T)
  have hB : 1 ≤ B := by
    have hexp : 1 ≤ Real.exp ((2 * C) * T) := Real.one_le_exp_iff.mpr (by positivity)
    simpa only [one_mul] using mul_le_mul hZ hexp zero_le_one (by linarith : 0 ≤ Z)
  refine ⟨B, C * (1 + B), hB, by positivity, ?_⟩
  intro M _ _ _ l r hlr F htime U hU e he hi hlower hupper hcurv hjets hinit x hx
  let G := closedSlabInterior hlr F
  let f := fun t => iteratedFDeriv ℝ (q + 1) ((F.metric t).pullbackCoefficients e) x
  have hf : ContDiffOn ℝ 1 f (Icc l r) :=
    (contDiffOn_pullback_spatialJet_time hlr F hU he (q + 1) hx).of_le (by simp)
  have hrate (t : ℝ) (ht : t ∈ Ioo l r) : ‖deriv f t‖ ≤ C * (1 + ‖f t‖) := by
    exact hevol G isOpen_Ioo hU he hi ht hx
      (hlower t (Ioo_subset_Icc_self ht) x hx)
      (hupper t (Ioo_subset_Icc_self ht) x hx)
      (hcurv t (Ioo_subset_Icc_self ht) x hx)
      (fun j hj hjq => (hjets t (Ioo_subset_Icc_self ht) x hx j hj hjq).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hA hj))
  have hbound (t : ℝ) (ht : t ∈ Icc l r) : ‖f t‖ ≤ B := by
    apply (norm_le_exp_of_interior_affine_bound hlr hf hC hZ (hinit x hx) hrate t ht).trans
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left htime (by positivity))) (by linarith : 0 ≤ Z)
  refine ⟨hbound, ?_⟩
  apply norm_sub_le_of_interior_deriv_bound hlr hf
  intro t ht
  exact (hrate t ht).trans (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (hbound t (Ioo_subset_Icc_self ht))) hC)

end PoincareConjecture.M44

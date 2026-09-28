import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Terminal.SpatialJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M30

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in




theorem exists_closed_spatialJet_time_lipschitz_constant
    (n d : ℕ) (K Z : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {M : Type u} [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {T : ℝ}, 0 < T → T ≤ 1 →
        ∀ (F : RicciFlow n M (Icc (-T) 0))
        {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        ∀ {τ : ℝ}, τ ∈ Ioo (-T) 0 →
        ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
        (∀ t ∈ Icc (-T) 0, ∀ v,
          a * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients e x v v ∧
          (F.metric t).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ j ≤ d, ∀ t ∈ Icc (-T) 0,
          (F.connection t).curvatureDerivativeNorm j (e x) ≤ K j) →
        (∀ j ≤ d, ‖iteratedFDeriv ℝ j ((F.metric τ).pullbackCoefficients e) x‖ ≤ Z j) →
        ∀ j ≤ d,
          (∀ t ∈ Icc (-T) 0,
            ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B) ∧
          (∀ s ∈ Icc (-T) 0, ∀ t ∈ Icc (-T) 0,
            ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x -
              iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients e) x‖ ≤ B * |t - s|) := by
  obtain ⟨B, hB, hbound⟩ :=
    SpacetimeBounds.exists_spatialJet_time_lipschitz_constant.{u} n d K Z hK ha hb
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ T hT hT1 F U hU e he hi τ hτ x hx hell hcurv hinit
  have htime : -T < (0 : ℝ) := neg_neg_of_pos hT
  have hne : (Ioo (-T) 0).Nontrivial := by
    refine ⟨-T / 2, ⟨by linarith, by linarith⟩,
      -T / 4, ⟨by linarith, by linarith⟩, by linarith⟩
  let Fint := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    Ioo_subset_Icc_self ordConnected_Ioo hne
  have hinterior {s t : ℝ} (hs : s ∈ Ioo (-T) 0) (ht : t ∈ Ioo (-T) 0)
      (j : ℕ) (hj : j ≤ d) :
      ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B ∧
      ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x -
        iteratedFDeriv ℝ j ((F.metric s).pullbackCoefficients e) x‖ ≤ B * |t - s| := by
    let l := min τ (min s t)
    let r := max τ (max s t)
    have hl : l ∈ Ioo (-T) 0 :=
      ⟨lt_min hτ.1 (lt_min hs.1 ht.1), (min_le_left _ _).trans_lt hτ.2⟩
    have hr : r ∈ Ioo (-T) 0 :=
      ⟨hτ.1.trans_le (le_max_left _ _), max_lt hτ.2 (max_lt hs.2 ht.2)⟩
    have hsub : Icc l r ⊆ Ioo (-T) 0 :=
      fun _ hv => ⟨hl.1.trans_le hv.1, hv.2.trans_lt hr.2⟩
    have hlen : r - l ≤ 1 := by linarith [hl.1, hr.2]
    have hτlr : τ ∈ Icc l r := ⟨min_le_left _ _, le_max_left _ _⟩
    have hslr : s ∈ Icc l r :=
      ⟨(min_le_right _ _).trans (min_le_left _ _),
        (le_max_left _ _).trans (le_max_right _ _)⟩
    have htlr : t ∈ Icc l r :=
      ⟨(min_le_right _ _).trans (min_le_right _ _),
        (le_max_right _ _).trans (le_max_right _ _)⟩
    have h := hbound Fint isOpen_Ioo hU he hi hsub hlen hτlr hx
      (fun v hv => hell v (Ioo_subset_Icc_self (hsub hv)))
      (fun q hq v hv => hcurv q hq v (Ioo_subset_Icc_self (hsub hv))) hinit j hj
    exact ⟨h.1 t htlr, h.2 s hslr t htlr⟩
  intro j hj
  let f := fun t => iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x
  have hcont : ContinuousOn f (Icc (-T) 0) := by
    have hjet := SpacetimeBounds.contDiffOn_spatialJet_within
      (F.contDiffOn_pullbackCoefficients_within hU he) (uniqueDiffOn_Icc htime) hU j
    intro t ht
    exact ((hjet (t, x) ⟨ht, hx⟩).comp t
      (show ContDiffWithinAt ℝ ∞ (fun s : ℝ => (s, x)) (Icc (-T) 0) t from
        contDiffWithinAt_id.prodMk contDiffWithinAt_const)
      (show MapsTo (fun s : ℝ => (s, x)) (Icc (-T) 0) (Icc (-T) 0 ×ˢ U) from
        fun _ hs => ⟨hs, hx⟩)).continuousWithinAt
  have hclosure {t : ℝ} (ht : t ∈ Icc (-T) 0) : t ∈ closure (Ioo (-T) 0) := by
    rwa [closure_Ioo htime.ne]
  change (∀ t ∈ Icc (-T) 0, ‖f t‖ ≤ B) ∧
    (∀ s ∈ Icc (-T) 0, ∀ t ∈ Icc (-T) 0, ‖f t - f s‖ ≤ B * |t - s|)
  constructor
  · intro t ht
    apply ContinuousWithinAt.closure_le (hclosure ht)
      ((hcont t ht).norm.mono Ioo_subset_Icc_self) continuousWithinAt_const
    exact fun s hs => (hinterior hs hs j hj).1
  · have hone {s : ℝ} (hs : s ∈ Ioo (-T) 0) {t : ℝ} (ht : t ∈ Icc (-T) 0) :
        ‖f t - f s‖ ≤ B * |t - s| := by
      apply ContinuousWithinAt.closure_le (hclosure ht)
        (((hcont t ht).sub continuousWithinAt_const).norm.mono Ioo_subset_Icc_self)
        (by fun_prop)
      exact fun v hv => (hinterior hs hv j hj).2
    intro s hs t ht
    apply ContinuousWithinAt.closure_le (hclosure hs)
      ((continuousWithinAt_const.sub (hcont s hs)).norm.mono Ioo_subset_Icc_self)
      (by fun_prop)
    exact fun v hv => hone hv ht

end PoincareConjecture.M30

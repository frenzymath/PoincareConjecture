import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.TimeControl

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SpacetimeBounds

theorem exists_closed_terminal_spatialJet_time_constant
    (n d : ℕ) (K Z : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {M : Type*} [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        {s T : ℝ} (F : RicciFlow n M (Ioc s T))
        {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
        ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
        (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
        ∀ {t : ℝ}, s < t → t < T → T - t ≤ 1 →
        ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
        (∀ r ∈ Ico t T, ∀ v,
          a * ‖v‖ ^ 2 ≤ (F.metric r).pullbackCoefficients e x v v ∧
          (F.metric r).pullbackCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ j ≤ d, ∀ r ∈ Ico t T,
          (F.connection r).curvatureDerivativeNorm j (e x) ≤ K j) →
        (∀ j ≤ d, ‖iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ Z j) →
        ∀ r ∈ Icc t T, ∀ j ≤ d,
          ‖iteratedFDeriv ℝ j ((F.metric r).pullbackCoefficients e) x -
            iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B * (r - t) := by
  obtain ⟨B, hB, htime⟩ := exists_terminal_spatialJet_time_constant n d K Z hK ha hb
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ s T F U hU e he hi t hst htT hlen x hx hell hcurv hinit r hr j hj
  obtain rfl | htr := hr.1.eq_or_lt
  · simp
  · let Fr := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
      (show Ioc s r ⊆ Ioc s T from fun q hq => ⟨hq.1, hq.2.trans hr.2⟩)
      ordConnected_Ioc
      (show (Ioc s r).Nontrivial from
        ⟨t, ⟨hst, htr.le⟩, r, ⟨hst.trans htr, le_rfl⟩, htr.ne⟩)
    exact htime Fr hU he hi hst htr (by linarith [hr.2]) hx
      (fun q hq => hell q ⟨hq.1, hq.2.trans_le hr.2⟩)
      (fun k hk q hq => hcurv k hk q ⟨hq.1, hq.2.trans_le hr.2⟩) hinit j hj

end PoincareConjecture.SpacetimeBounds

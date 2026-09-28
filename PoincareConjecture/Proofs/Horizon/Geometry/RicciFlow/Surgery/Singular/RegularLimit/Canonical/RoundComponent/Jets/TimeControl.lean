import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Terminal.SpatialJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SpacetimeBounds

theorem exists_terminal_spatialJet_time_constant
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
        ∀ j ≤ d,
          ‖iteratedFDeriv ℝ j ((F.metric T).pullbackCoefficients e) x -
            iteratedFDeriv ℝ j ((F.metric t).pullbackCoefficients e) x‖ ≤ B * (T - t) := by
  obtain ⟨B, hB, htime⟩ := exists_spatialJet_time_lipschitz_constant n d K Z hK ha hb
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ _ s T F U hU e he hi t hst htT hlen x hx hell hcurv hinit j hj
  let Fint := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Ioo s T ⊆ Ioc s T from fun r hr => ⟨hr.1, hr.2.le⟩) ordConnected_Ioo
    (show (Ioo s T).Nontrivial from
      ⟨(2 * s + T) / 3, ⟨by linarith, by linarith⟩,
        (s + 2 * T) / 3, ⟨by linarith, by linarith⟩, by linarith⟩)
  let f := fun r : ℝ => iteratedFDeriv ℝ j ((F.metric r).pullbackCoefficients e) x
  have hjoint := contDiffOn_spatialJet_within
    (F.contDiffOn_pullbackCoefficients_within hU he) (uniqueDiffOn_Ioc s T) hU j
  have hcont : ContinuousOn f (Icc t T) := by
    exact hjoint.continuousOn.comp (f := fun r : ℝ => (r, x))
      (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨⟨hst.trans_le hr.1, hr.2⟩, hx⟩)
  have hbound (r : ℝ) (hr : r ∈ Ico t T) : ‖f r - f t‖ ≤ B * (r - t) := by
    have hsub : Icc t r ⊆ Ioo s T := fun q hq =>
      ⟨hst.trans_le hq.1, hq.2.trans_lt hr.2⟩
    have hsub' : Icc t r ⊆ Ico t T := fun q hq => ⟨hq.1, hq.2.trans_lt hr.2⟩
    have h := (htime Fint isOpen_Ioo hU he hi hsub
      (by linarith [hr.2] : r - t ≤ 1) (show t ∈ Icc t r from ⟨le_rfl, hr.1⟩)
      hx (fun q hq => hell q (hsub' hq))
      (fun k hk q hq => hcurv k hk q (hsub' hq)) hinit j hj).2
      t ⟨le_rfl, hr.1⟩ r ⟨hr.1, le_rfl⟩
    change ‖f r - f t‖ ≤ B * |r - t| at h
    simpa only [abs_of_nonneg (sub_nonneg.mpr hr.1)] using h
  have hterminal : T ∈ closure (Ico t T) := by
    rw [closure_Ico htT.ne]
    exact ⟨htT.le, le_rfl⟩
  have hleft : ContinuousWithinAt (fun r => ‖f r - f t‖) (Ico t T) T :=
    (((hcont T ⟨htT.le, le_rfl⟩).sub continuousWithinAt_const).norm).mono
      Ico_subset_Icc_self
  have hright : ContinuousWithinAt (fun r : ℝ => B * (r - t)) (Ico t T) T :=
    (continuous_const.mul (continuous_id.sub continuous_const)).continuousWithinAt
  exact ContinuousWithinAt.closure_le hterminal hleft hright hbound

end PoincareConjecture.SpacetimeBounds

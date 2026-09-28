import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowTimeJetBounds
import PoincareConjecture.Proofs.M34.Mathlib.TerminalLipschitz











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture



theorem RiemannianMetric.pullbackCoefficients_id {n : ℕ}
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    g.pullbackCoefficients id = g.euclideanCoefficients := by
  ext x u v
  change g.inner x (mfderiv (𝓡 n) (𝓡 n) id x u)
    (mfderiv (𝓡 n) (𝓡 n) id x v) = g.inner x u v
  rw [mfderiv_id]
  rfl

namespace M34



theorem partialFlow_compactPullback_spatialJet_time_lipschitz
    (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {S B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ D : ℝ≥0, ∀ {U : Set StandardCapSpace}, IsOpen U →
      ∀ {e : StandardCapSpace → StandardCapSpace}, ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U →
      (∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) →
      (∀ x ∈ U, ∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
          (mfderiv (𝓡 3) (𝓡 3) e x v)) →
      ∀ x ∈ K, x ∈ U → LipschitzOnWith D
        (fun t => iteratedFDeriv ℝ m ((F.flow.metric t).pullbackCoefficients e) x)
        (Ico 0 S) := by
  obtain ⟨D, hD, hbound⟩ := partialFlow_compactPullback_timeDeriv_spatialJet_bound
    P E0 F hS hSF hB hfull hK m
  refine ⟨⟨D, hD⟩, ?_⟩
  intro U hU e he hinv hmetric x hx hxU
  have hsub : Ico 0 S ⊆ Ico 0 F.lifetime := fun _ ht => ⟨ht.1, ht.2.trans_le hSF⟩
  have hcoeff := F.flow.smooth.contDiffOn_spacetime_pullbackCoefficients hU he
  have hjoint : ContDiffOn ℝ ∞
      (fun p : ℝ × StandardCapSpace =>
        iteratedFDeriv ℝ m ((F.flow.metric p.1).pullbackCoefficients e) p.2)
      (Ico 0 S ×ˢ U) :=
    (hcoeff.iteratedFDeriv_snd_of_isOpen hU m).mono (prod_mono hsub (Subset.refl U))
  apply lipschitzOnWith_of_interior_deriv_bound_Ico hD
  · apply hjoint.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
    exact fun _ ht => ⟨ht, hxU⟩
  · intro t ht
    have hreg := hjoint.mono (prod_mono Ioo_subset_Ico_self (Subset.refl U))
    have hat := hreg.contDiffAt (x := (t, x)) ((isOpen_Ioo.prod hU).mem_nhds ⟨ht, hxU⟩)
    exact (hat.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  · exact fun t ht => hbound hU he hinv hmetric t ht x hx hxU



theorem partialFlow_compact_spatialJet_time_lipschitz
    (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {S B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ D : ℝ≥0, ∀ x ∈ K, LipschitzOnWith D
      (fun t => iteratedFDeriv ℝ m (F.flow.metric t).euclideanCoefficients x) (Ico 0 S) := by
  obtain ⟨D, hD⟩ := partialFlow_compactPullback_spatialJet_time_lipschitz
    P E0 F hS hSF hB hfull hK m
  refine ⟨D, ?_⟩
  intro x hx
  have hinv (y : StandardCapSpace) (_hy : y ∈ (univ : Set StandardCapSpace)) :
      (mfderiv (𝓡 3) (𝓡 3) id y).IsInvertible := by
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hmetric (y : StandardCapSpace) (_hy : y ∈ (univ : Set StandardCapSpace))
      (u v : TangentSpace (𝓡 3) y) : g0.metric.inner y u v =
      g0.metric.inner (id y) (mfderiv (𝓡 3) (𝓡 3) id y u)
        (mfderiv (𝓡 3) (𝓡 3) id y v) := by
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply]
  simpa only [RiemannianMetric.pullbackCoefficients_id] using
    hD isOpen_univ contMDiffOn_id hinv hmetric x hx (mem_univ x)



theorem partialFlow_spatialJet_terminal_limit_exists
    (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {S B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    (m : ℕ) (x : StandardCapSpace) :
    ∃ z : StandardCapSpace [×m]→L[ℝ] SpacetimeBounds.MetricCoefficient 3,
      Tendsto (fun t => iteratedFDeriv ℝ m (F.flow.metric t).euclideanCoefficients x)
        (𝓝[<] S) (𝓝 z) := by
  obtain ⟨D, hD⟩ := partialFlow_compact_spatialJet_time_lipschitz P E0 F
    hS hSF hB hfull (isCompact_singleton (x := x)) m
  obtain ⟨z, hz, _hmod⟩ := (hD x (mem_singleton x)).exists_terminal_limit hS
  exact ⟨z, hz⟩

end M34
end PoincareConjecture

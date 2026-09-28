import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowSpatialJetBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open SpacetimeBounds SpacetimeBounds.Bootstrap

set_option synthInstance.maxHeartbeats 100000 in

theorem partialFlow_compactPullback_timeDeriv_spatialJet_bound
    (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) {S B : ℝ} (hS : 0 < S)
    (hSF : S ≤ F.lifetime) (hB : 0 < B)
    (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
      (F.flow.connection t).curvatureTensorNorm x ≤ B)
    {K : Set StandardCapSpace} (hK : IsCompact K) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {U : Set StandardCapSpace}, IsOpen U →
      ∀ {e : StandardCapSpace → StandardCapSpace}, ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U →
      (∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) e x).IsInvertible) →
      (∀ x ∈ U, ∀ u v : TangentSpace (𝓡 3) x, g0.metric.inner x u v =
        g0.metric.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x u)
          (mfderiv (𝓡 3) (𝓡 3) e x v)) →
      ∀ t ∈ Ioo 0 S, ∀ x ∈ K, x ∈ U →
        ‖deriv (fun s => iteratedFDeriv ℝ m ((F.flow.metric s).pullbackCoefficients e) x) t‖ ≤
          D := by
  obtain ⟨a, _b, ha, _hb, hell⟩ :=
    partialFlow_compactPullback_ellipticity P F hSF hB.le hfull hK
  obtain ⟨G, hG, hjets⟩ := partialFlow_compactPullback_spatialJet_bounds P E0 F
    hS hSF hB hfull hK (2 + m)
  obtain ⟨L, hL, hLU, hbox⟩ := exists_compact_elliptic_jet_box 3 m ha G
  let Q := operator 2 (jetRicciFlowOperator 3) m
  have hQ := contDiffOn_operator (isOpen_jetRicciFlowDomain 3)
    (contDiffOn_jetRicciFlowOperator 3) m
  obtain ⟨D, hD⟩ := hL.exists_bound_of_continuousOn (f := Q) (hQ.continuousOn.mono hLU)
  refine ⟨max D 0, le_max_right _ _, ?_⟩
  intro U hU e he hinv hmetric t ht x hx hxU
  let f := fun z : ℝ × StandardCapSpace => (F.flow.metric z.1).pullbackCoefficients e z.2
  have hsub : Ioo 0 S ⊆ Ico 0 F.lifetime := fun _ hs => ⟨hs.1.le, hs.2.trans_le hSF⟩
  have hne : (Ioo 0 S).Nontrivial := by
    refine ⟨S / 3, ⟨?_, ?_⟩, 2 * S / 3, ⟨?_, ?_⟩, ?_⟩ <;> linarith
  let H := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F.flow hsub ordConnected_Ioo hne
  have hf : ContDiffOn ℝ ∞ f (Ioo 0 S ×ˢ U) :=
    (F.flow.smooth.contDiffOn_spacetime_pullbackCoefficients hU he).mono
      (prod_mono hsub (Subset.refl U))
  have hdomain (z : ℝ × StandardCapSpace) (hz : z ∈ Ioo 0 S ×ˢ U) :
      spatialJet 2 f z ∈ jetRicciFlowDomain 3 := by
    change ((twoJetProjection 3 (spatialJet 2 f z)).1).IsInvertible
    rw [twoJetProjection_spatialJet]
    exact (F.flow.metric z.1).isInvertible_pullbackCoefficients (hinv z.2 hz.2).injective
  have hevol (z : ℝ × StandardCapSpace) (hz : z ∈ Ioo 0 S ×ˢ U) :
      deriv (fun s => f (s, z.2)) z.1 = jetRicciFlowOperator 3 (spatialJet 2 f z) := by
    rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
    exact deriv_pullbackCoefficients_eq_ricciFlowOperator H isOpen_Ioo hU he hinv hz.1 hz.2
  have heq := deriv_spatialJet_eq_operator (isOpen_jetRicciFlowDomain 3)
    (contDiffOn_jetRicciFlowOperator 3) hf isOpen_Ioo hU hdomain hevol m
    (z := (t, x)) ⟨ht, hxU⟩
  change ‖deriv (fun s => iteratedFDeriv ℝ m (fun y => f (s, y)) x) t‖ ≤ max D 0
  rw [heq]
  apply (hD _ ?_).trans (le_max_left _ _)
  apply hbox
  · apply (pi_norm_le_iff_of_nonneg (zero_le_one.trans hG)).mpr
    intro j
    exact hjets j (by omega) hU he hinv hmetric t ⟨ht.1.le, ht.2⟩ x hx hxU
  · exact fun v => (hell t ⟨ht.1.le, ht.2⟩ x hx e (hmetric x hxU) v).1

end PoincareConjecture.M34

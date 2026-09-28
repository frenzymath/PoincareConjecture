import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Coordinates.CompactControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Bootstrap.Evolution








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem exists_uniform_coordinate_spacetime_jet_tail
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {q : M} (hq : q ∈ H.reference.regularLimitSet) :
    ∃ s r : ℝ, H.reference.tMinus < s ∧ s < T ∧ 0 < r ∧
      let c := extChartAt (𝓡 3) q
      Metric.closedBall (c q) r ⊆ c.target ∧
      c.symm '' Metric.closedBall (c q) r ⊆ H.reference.regularLimitSet ∧
      ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ioo s T,
        ∀ z ∈ Metric.closedBall (c q) r,
          ‖iteratedFDeriv ℝ m (fun p : ℝ × EuclideanSpace ℝ (Fin 3) =>
            (H.reference.flow.metric p.1).pullbackCoefficients c.symm p.2) (t, z)‖ ≤ B := by
  obtain ⟨s₁, r, a, b, hs₁, hs₁T, hr, ha, _, htarget, hreg, hell, _⟩ :=
    H.exists_uniform_coordinate_neighborhood P04 hq
  let c := extChartAt (𝓡 3) q
  let A := Metric.closedBall (c q) r
  obtain ⟨s₂, _, hs₂T, hspatial⟩ := H.exists_uniform_coordinate_metric_jet_tail_on_compact
    P04 q (isCompact_closedBall (c q) r) htarget hreg
  let s := max s₁ s₂
  have hs : H.reference.tMinus < s := hs₁.trans_le (le_max_left _ _)
  have hsT : s < T := max_lt hs₁T hs₂T
  have ht₁ {t : ℝ} (ht : t ∈ Ioo s T) : t ∈ Ico s₁ T :=
    ⟨(le_max_left _ _).trans ht.1.le, ht.2⟩
  have ht₂ {t : ℝ} (ht : t ∈ Ioo s T) : t ∈ Ico s₂ T :=
    ⟨(le_max_right _ _).trans ht.1.le, ht.2⟩
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow H.reference.flow
    (Ioo_subset_Ico_self : Ioo H.reference.tMinus T ⊆ Ico H.reference.tMinus T)
    ordConnected_Ioo ⟨s, ⟨hs, hsT⟩, (s + T) / 2,
      ⟨by linarith, by linarith⟩, by linarith⟩
  let E := EuclideanSpace ℝ (Fin 3)
  let f : ℝ × E → MetricCoefficient 3 :=
    fun p => (H.reference.flow.metric p.1).pullbackCoefficients c.symm p.2
  let S := Ioo s T ×ˢ A
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target := contMDiffOn_extChartAt_symm q
  have hi (z : E) (hz : z ∈ c.target) :
      (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible :=
    Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hz
  have hf : ContDiffOn ℝ ∞ f (Ioo H.reference.tMinus T ×ˢ c.target) :=
    G.contDiffOn_pullbackCoefficients isOpen_Ioo (isOpen_extChartAt_target q) he
  have hS : S ⊆ Ioo H.reference.tMinus T ×ˢ c.target :=
    fun _ hz => ⟨⟨hs.trans hz.1.1, hz.1.2⟩, htarget hz.2⟩
  have hrange (z : ℝ × E) (hz : z ∈ Ioo H.reference.tMinus T ×ˢ c.target) :
      spatialJet 2 f z ∈ jetRicciFlowDomain 3 := by
    change ((twoJetProjection 3 (spatialJet 2 f z)).1).IsInvertible
    rw [twoJetProjection_spatialJet]
    exact (H.reference.flow.metric z.1).isInvertible_pullbackCoefficients
      (hi z.2 hz.2).injective
  have hevol (z : ℝ × E) (hz : z ∈ Ioo H.reference.tMinus T ×ˢ c.target) :
      deriv (fun t => f (t, z.2)) z.1 = jetRicciFlowOperator 3 (spatialJet 2 f z) := by
    rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
    exact deriv_pullbackCoefficients_eq_ricciFlowOperator G
      isOpen_Ioo (isOpen_extChartAt_target q) he hi hz.1 hz.2
  have hall (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ S, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2‖ ≤ B := by
    induction k with
    | zero =>
      obtain ⟨B, hB, hb⟩ := hspatial 0
      refine ⟨B, hB, ?_⟩
      intro z hz j hj
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      exact hb z.1 (ht₂ hz.1) z.2 hz.2
    | succ k ih =>
      obtain ⟨B, hB, hb⟩ := ih
      obtain ⟨C, hC, hc⟩ := hspatial (k + 1)
      refine ⟨max B C, le_max_of_le_left hB, ?_⟩
      intro z hz j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · exact (hc z.1 (ht₂ hz.1) z.2 hz.2).trans (le_max_right _ _)
      · exact (hb z hz j (by omega)).trans (le_max_left _ _)
  have hspatial' (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ _w : Unit in pure (),
      ∀ z ∈ S, ‖iteratedFDeriv ℝ j (fun x => f (z.1, x)) z.2‖ ≤ B := by
    obtain ⟨B, hB, hb⟩ := hall j
    exact ⟨B, hB, Eventually.of_forall (fun _ z hz => hb z hz j le_rfl)⟩
  have hcompact (j : ℕ) : ∃ K : Set (Jet E (MetricCoefficient 3) (2 + j)),
      IsCompact K ∧ K ⊆ (baseProjection 2 j) ⁻¹' jetRicciFlowDomain 3 ∧
      ∀ᶠ _w : Unit in pure (), MapsTo (spatialJet (2 + j) f) S K := by
    obtain ⟨B, hB, hb⟩ := hall (2 + j)
    obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box 3 j ha B
    refine ⟨K, hK, hKU, Eventually.of_forall (fun _ z hz => ?_)⟩
    apply hbox
    · exact (pi_norm_le_iff_of_nonneg hB).mpr (fun d => hb z hz d (by omega))
    · intro v
      exact (hell z.1 (ht₁ hz.1) z.2 hz.2 v).1
  refine ⟨s, r, hs, hsT, hr, htarget, hreg, ?_⟩
  intro m
  obtain ⟨B, hB, hb⟩ := eventuallyBounded_spacetime_jets (pure ())
    (isOpen_jetRicciFlowDomain 3) (contDiffOn_jetRicciFlowOperator 3)
    (fun _ : Unit => f) (fun _ => Ioo H.reference.tMinus T)
    (fun _ => c.target) (fun _ => S) (fun _ => hf)
    (fun _ => isOpen_Ioo) (fun _ => isOpen_extChartAt_target q)
    (fun _ => hS) (fun _ => hrange) (fun _ => hevol) hspatial' hcompact m
  exact ⟨B, hB, fun t ht z hz => (eventually_pure.mp hb) (t, z) ⟨ht, hz⟩⟩

end PoincareConjecture.SingularTimeAssumptions

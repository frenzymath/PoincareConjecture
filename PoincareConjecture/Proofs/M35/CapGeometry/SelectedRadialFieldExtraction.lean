import PoincareConjecture.Proofs.M35.CapGeometry.SelectedRadialFieldBounds
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness Poincare.Analysis.Calculus

local notation "V" => EuclideanSpace ℝ (Fin 3)

noncomputable def selectedCoordinateRadialField
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (coordinate : V → L.limit.sliceCarrier.carrier) (k : ℕ) : V → V :=
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) Q hQ
  let f : V → StandardCapSpace := fun z => ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ (coordinate z)).val
  pullback ℝ f (radialUnitField G)

theorem blowupSequence_coordinate_radial_smooth_subsequence
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : V → L.limit.sliceCarrier.carrier)
      (_hc : ContMDiff (𝓡 3) (𝓡 3) ∞ coordinate)
      (_hi : ∀ z, (mfderiv (𝓡 3) (𝓡 3) coordinate z).IsInvertible)
      (g : RiemannianMetric 3 V)
      (_hg : g.euclideanCoefficients = (L.limit.flow.metric 0).pullbackCoefficients coordinate)
      (Ω : Set V) (_hΩ : IsOpen Ω) (_hcompact : IsCompact (closure Ω)),
      ∃ (sigma : ℕ → ℕ) (Z : V → V), StrictMono sigma ∧ ContDiffOn ℝ ∞ Z Ω ∧
        ∀ (m : ℕ) (K : Set V), IsCompact K → K ⊆ Ω →
          TendstoUniformlyOn (fun k y => iteratedFDeriv ℝ m
            (selectedCoordinateRadialField P E t x ht hR L coordinate (sigma k)) y)
            (iteratedFDeriv ℝ m Z) atTop K := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate hc hi g hg Ω hΩ hcompact
  let Zseq := selectedCoordinateRadialField P E t x ht hR L coordinate
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (blowupSequence_coordinate_radial_domain P E t x ht hR hd L
      coordinate hc hi (closure Ω) hcompact)
  let mu (k : ℕ) := k + N
  have hmu : StrictMono mu := fun i j hij => Nat.add_lt_add_right hij N
  have hs (k : ℕ) : ContDiffOn ℝ ∞ (Zseq (mu k)) Ω := by
    intro z hz
    have h := (hN (mu k) (Nat.le_add_left N k) z (subset_closure hz)).1.self_of_nhds
    have hf := contMDiffAt_iff_contDiffAt.mp h.1
    let f : V → StandardCapSpace := fun y => ((L.embedding (mu k)).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (mu k)).le, le_rfl⟩ (coordinate y)).val
    have hif : (fderiv ℝ f z).IsInvertible := by
      simpa only [mfderiv_eq_fderiv] using h.2.1
    exact (euclidean_radial_pullback_contDiffAt _ hf hif h.2.2).contDiffWithinAt
  have hb : LocallyEventuallyBoundedDerivatives Ω (fun k => Zseq (mu k)) := by
    intro K hK _hKΩ m
    obtain ⟨C, hC⟩ := blowupSequence_coordinate_radial_jets_bounded P E t x ht hR hd L
      coordinate hc hi g hg K hK m
    exact ⟨C, hmu.tendsto_atTop.eventually hC⟩
  obtain ⟨H⟩ := exists_smoothSubsequenceExtraction hΩ (fun k => Zseq (mu k)) hs hb
  refine ⟨mu ∘ H.subsequence, H.limit,
    hmu.comp H.subsequence_strictMono, H.limit_contDiffOn, ?_⟩
  exact H.iteratedFDeriv_tendsto_uniformlyOn

end PoincareConjecture.M35.OrdinaryRealization

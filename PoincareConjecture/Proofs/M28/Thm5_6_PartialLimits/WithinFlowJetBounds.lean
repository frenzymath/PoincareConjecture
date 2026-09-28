import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinRicciJetBounds
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.WithinMetricCoefficients
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RicciFlow

open SpacetimeBounds SpacetimeBounds.Bootstrap




theorem deriv_pullbackCoefficients_eq_ricciFlowOperator_of_mem_interior
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    {t : ℝ} (ht : t ∈ interior J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    deriv (fun s => (F.metric s).pullbackCoefficients e x) t =
      ricciFlowOperator n (metricTwoJet ((F.metric t).pullbackCoefficients e) x) := by
  obtain ⟨a, b, htab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (mem_interior_iff_mem_nhds.mp ht)
  obtain ⟨s, has, hst⟩ := exists_between htab.1
  have hnontriv : (Ioo a b).Nontrivial :=
    ⟨s, ⟨has, hst.trans htab.2⟩, t, htab, ne_of_lt hst⟩
  let F' := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub
    ordConnected_Ioo hnontriv
  exact deriv_pullbackCoefficients_eq_ricciFlowOperator F' isOpen_Ioo hU he hi htab hx

set_option synthInstance.maxHeartbeats 100000 in






theorem eventuallyBounded_within_pullbackCoefficients_of_spatial_bounds
    {n : ℕ} {α : Type*} {M : α → Type*}
    [∀ w, TopologicalSpace (M w)]
    [∀ w, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M w)]
    [∀ w, IsManifold (𝓡 n) ∞ (M w)]
    (l : Filter α) (J : α → Set ℝ) (F : ∀ w, RicciFlow n (M w) (J w))
    (U : α → Set (EuclideanSpace ℝ (Fin n)))
    (e : ∀ w, EuclideanSpace ℝ (Fin n) → M w)
    (T S : α → Set (ℝ × EuclideanSpace ℝ (Fin n)))
    (hJ : ∀ w, UniqueDiffOn ℝ (J w)) (hU : ∀ w, IsOpen (U w))
    (he : ∀ w, ContMDiffOn (𝓡 n) (𝓡 n) ∞ (e w) (U w))
    (hi : ∀ w y, y ∈ U w → (mfderiv (𝓡 n) (𝓡 n) (e w) y).IsInvertible)
    (hT : ∀ w, T w ⊆ interior (J w) ×ˢ U w)
    (hS : ∀ w, S w ⊆ (J w ×ˢ U w) ∩ closure (T w))
    (hspatial : ∀ q, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l, ∀ z ∈ T w, ∀ j ≤ q,
      ‖iteratedFDeriv ℝ j ((F w).metric z.1 |>.pullbackCoefficients (e w)) z.2‖ ≤ B)
    {a : ℝ} (ha : 0 < a)
    (hell : ∀ᶠ w in l, ∀ z ∈ T w, ∀ v,
      a * ‖v‖ ^ 2 ≤ ((F w).metric z.1).pullbackCoefficients (e w) z.2 v v) :
    ∀ m, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ w in l, ∀ z ∈ S w,
      ‖iteratedFDerivWithin ℝ m
        (fun z => ((F w).metric z.1).pullbackCoefficients (e w) z.2)
        (J w ×ˢ U w) z‖ ≤ B := by
  apply eventuallyBounded_within_ricci_spacetime_jets l
    (fun w z => ((F w).metric z.1).pullbackCoefficients (e w) z.2)
    J U T S hJ hU
    (fun w => (F w).smooth.contDiffOn_spacetime_pullbackCoefficients_within (hU w) (he w))
    hT hS ?_ ?_ hspatial ha hell
  · intro w z hz
    change ((twoJetProjection n (spatialJet 2
      (fun z => ((F w).metric z.1).pullbackCoefficients (e w) z.2) z)).1).IsInvertible
    rw [twoJetProjection_spatialJet]
    exact ((F w).metric z.1).isInvertible_pullbackCoefficients (hi w z.2 hz.2).injective
  · intro w z hz
    rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
    exact (F w).deriv_pullbackCoefficients_eq_ricciFlowOperator_of_mem_interior
      (hU w) (he w) (hi w) hz.1 hz.2

end PoincareConjecture.RicciFlow

import PoincareConjecture.Proofs.M32.Mathlib.ProductSeparator
import PoincareConjecture.Proofs.M32.Claim11_35.FiniteProductFactor
import Mathlib.Topology.Connected.LocallyPathConnected

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

theorem blowupLimit_exists_compact_product_on_closed_slab
    (P : RepairedHornSelectionPredecessors.{u}) {T₀ : ℝ≥0∞}
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval T₀))
    {T : ℝ} (hT : 0 < T) (hsub : Icc (-T) 0 ⊆ blowupBackwardInterval T₀)
    (gamma : ℝ → L.carrier.carrier)
    (hgamma : ∀ s t : ℝ,
      (L.flow.metric 0).edist (gamma s) (gamma t) = ENNReal.ofReal |s - t|)
    {K : Set L.carrier.carrier} (hK : IsCompact K) {R₀ : ℝ}
    (hsep : ∀ t : ℝ, R₀ < t → ¬ JoinedIn Kᶜ (gamma (-t)) (gamma t)) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ t ∈ Icc (-T) 0, ∀ x,
        |(L.flow.connection t).curvatureTensorNorm x| ≤ B) ∧
      ∃ C : FlowCarrier.{u} 2, CompactSpace C.carrier ∧
        ∃ H : RicciFlow 2 C.carrier (Icc (-T) 0),
          (∀ t ∈ Icc (-T) 0, MetricComplete (H.metric t)) ∧
          (∀ t ∈ Icc (-T) 0, ∀ y, (H.connection t).NonnegativeCurvatureOperator y) ∧
          (∀ t ∈ Icc (-T) 0, ∀ y, (H.connection t).curvatureTensorNorm y ≤ B) ∧
          ∃ e : (C.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ L.carrier.carrier,
            (∀ z, (L.flow.metric 0).busemann gamma (e z) = z.2) ∧
            (∀ t ∈ Icc (-T) 0, ∀ (z : C.carrier × ℝ)
              (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
              (L.flow.metric t).inner (e z)
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z v)
                (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) e z w) =
                  (H.metric t).inner z.1 v.1 w.1 + v.2 * w.2) ∧
            (∀ t ∈ Icc (-T) 0, ∀ x,
              (H.connection t).scalarCurvature (e.symm x).1 =
                (L.flow.connection t).scalarCurvature x) ∧
            (∀ t ∈ Icc (-T) 0, ∀ x,
              (H.connection t).curvatureTensorNorm (e.symm x).1 =
                (L.flow.connection t).curvatureTensorNorm x) ∧
            (H.connection 0).scalarCurvature (e.symm L.base).1 = 1 := by
  obtain ⟨B, hB, hbound, C, H, hc, hop, hnorm, e, hcoord, hm, hs, hn, hbase⟩ :=
    blowupLimit_exists_fixed_product_on_closed_slab P L hT hsub gamma hgamma
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let : LocallyPathConnectedSpace C.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier
  let : PathConnectedSpace C.carrier := PathConnectedSpace.of_locallyPathConnectedSpace
  let : ConnectedSpace L.carrier.carrier := L.connectedSpace
  have hheight (t : ℝ) : (e.toHomeomorph.symm (gamma t)).2 = t := by
    have h := hcoord (e.symm (gamma t))
    rw [e.apply_symm_apply] at h
    exact h.symm.trans ((L.flow.metric 0).busemann_apply_line hgamma t)
  have hcompact : IsCompact (univ : Set C.carrier) :=
    isCompact_univ_of_separated_product_line e.toHomeomorph gamma hheight hK hsep
  exact ⟨B, hB, hbound, C, ⟨hcompact⟩, H, hc, hop, hnorm, e, hcoord, hm, hs, hn, hbase⟩

end PoincareConjecture.M32

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ModelGeometry.QuotientVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ModelGeometry.ProductVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Models










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} {G : ShrinkingSolitonFlow S}

theorem SphereLineProductCertificate.normalized_ball_volume
    (C : SphereLineProductCertificate G) (p : M) :
    (G.flow.metric (-1)).volumeMeasure ((G.flow.metric (-1)).ball p (1 / 4)) =
      ENNReal.ofReal universalNoncollapseModelVolume := by
  let := C.surface_topology
  let := C.product_charted
  let := C.product_manifold
  let : MeasurableSpace (C.surface × ℝ) := borel _
  let : BorelSpace (C.surface × ℝ) := ⟨rfl⟩
  let : T3Space (C.surface × ℝ) := C.product_equiv.toHomeomorph.t3Space
  have h := RiemannianMetric.volumeMeasure_ball_diffeomorph
    (G.flow.metric (-1)) (C.product_metric (-1)) C.product_equiv
    (C.flow_isometric_to_product (-1) (by norm_num)) p (1 / 4)
  exact h.trans (C.toSphereLineProductData.normalized_ball_volume (C.product_equiv p))

theorem QuotientSphereLineCertificate.normalized_ball_volume_lower
    (q : QuotientSphereLineCertificate G) (p : M) :
    ENNReal.ofReal universalNoncollapseModelVolume ≤
      (G.flow.metric (-1)).volumeMeasure ((G.flow.metric (-1)).ball p (1 / 4)) := by
  let := q.cover_topology
  let := q.cover_charted
  let := q.cover_manifold
  let := q.product.surface_topology
  let := q.product.surface_charted
  let := q.product.surface_manifold
  let := q.product.product_charted
  let := q.product.product_manifold
  let := q.quotient_topology
  let := q.quotient_charted
  let := q.quotient_manifold
  let : MeasurableSpace (q.product.surface × ℝ) := borel _
  let : BorelSpace (q.product.surface × ℝ) := ⟨rfl⟩
  let : MeasurableSpace q.quotient_carrier := borel _
  let : BorelSpace q.quotient_carrier := ⟨rfl⟩
  let : T3Space q.product.surface := q.product.surface_sphere.toHomeomorph.isEmbedding.t3Space
  obtain ⟨e, he⟩ := q.flow_isometric_to_quotient
  let : T3Space q.quotient_carrier := e.toHomeomorph.t3Space
  obtain ⟨z, hz⟩ := q.quotient_map_surjective (e p)
  have hvol := q.product_ball_volume_le_quotient_ball_volume z
  rw [q.product.normalized_ball_volume z, hz] at hvol
  have h := RiemannianMetric.volumeMeasure_ball_diffeomorph
    (G.flow.metric (-1)) (q.quotient_metric (-1)) e
    (he (-1) (by norm_num)) p (1 / 4)
  exact hvol.trans_eq h.symm

theorem ThreeDimensionalSolitonModel.compactRound_or_normalized_ball_volume_lower
    (C : ThreeDimensionalSolitonModel S G) :
    Nonempty (CompactRoundShrinkingModel G) ∨
      ∀ p : M, ENNReal.ofReal universalNoncollapseModelVolume ≤
        (G.flow.metric (-1)).volumeMeasure ((G.flow.metric (-1)).ball p (1 / 4)) := by
  cases C with
  | compactRound c => exact Or.inl ⟨c⟩
  | sphereLine c => exact Or.inr (fun p => (c.normalized_ball_volume p).ge)
  | quotientSphereLine q => exact Or.inr q.normalized_ball_volume_lower

theorem ThreeDimensionalSolitonModel.normalized_ball_volume_lower [NoncompactSpace M]
    (C : ThreeDimensionalSolitonModel S G) (p : M) :
    ENNReal.ofReal universalNoncollapseModelVolume ≤
      (G.flow.metric (-1)).volumeMeasure ((G.flow.metric (-1)).ball p (1 / 4)) := by
  rcases C.compactRound_or_normalized_ball_volume_lower with hc | h
  · obtain ⟨c⟩ := hc
    exact ((not_compactSpace_iff.mpr (inferInstance : NoncompactSpace M)) c.compact).elim
  · exact h p

end PoincareConjecture

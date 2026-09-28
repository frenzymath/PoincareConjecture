import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.CollarOverlap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Overlaps.Metric












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

include hd in
theorem collarOverlaps_disjoint : Pairwise (fun i j =>
    Disjoint ((R i).collarOverlap U hU).source ((R j).collarOverlap U hU).source) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rw [(R i).collarOverlap_source] at hxi
  rw [(R j).collarOverlap_source] at hxj
  exact Set.disjoint_left.mp (hd hij) hxi hxj

def cutSystem : Poincare.Gluing.OverlapSystem
    (Piece U (fun i => (R i).output.carrier)) :=
  overlaps (fun i => (R i).collarOverlap U hU) (collarOverlaps_disjoint I R U hU hd)

theorem cutSystem_smooth (i j : Option ι) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ ((cutSystem I R U hU hd).transition i j)
      ((cutSystem I R U hU hd).transition i j).source :=
  overlaps_smooth _ _ (fun i => (R i).collarOverlap_smooth U hU)
    (fun i => (R i).collarOverlap_inverse_smooth U hU) i j

include hc in
theorem cutSystem_closed (i j : Option ι) :
    IsClosed {p : Piece U (fun i => (R i).output.carrier) i ×
        Piece U (fun i => (R i).output.carrier) j |
      (cutSystem I R U hU hd).Rel ⟨i, p.1⟩ ⟨j, p.2⟩} :=
  overlaps_closed _ _ (fun i => (R i).collarOverlap_closed_graph U hU (hc i)) i j

def cutPieceMetric := pieceMetric (S.openSubsetMetric U g) (fun i => (R i).metric)

theorem cutSystem_metric (i j : Option ι)
    (x : Piece U (fun i => (R i).output.carrier) i)
    (hx : x ∈ ((cutSystem I R U hU hd).transition i j).source)
    (a b : TangentSpace (𝓡 3) x) :
    (cutPieceMetric I R U i).inner x a b =
      (cutPieceMetric I R U j).inner ((cutSystem I R U hU hd).transition i j x)
        (mfderiv (𝓡 3) (𝓡 3) ((cutSystem I R U hU hd).transition i j) x a)
        (mfderiv (𝓡 3) (𝓡 3) ((cutSystem I R U hU hd).transition i j) x b) :=
  overlaps_metric _ _ (fun i => (R i).collarOverlap_smooth U hU)
    (fun i => (R i).collarOverlap_inverse_smooth U hU)
    (S.openSubsetMetric U g) (fun i => (R i).metric)
    (fun i x hx a b => ((R i).collarOverlap_metric U hU x hx a b).symm) i j x hx a b

variable [Countable ι]

@[implicit_reducible]
def cutCarrier : GeneralizedSliceCarrier.{u} :=
  carrier (cutSystem I R U hU hd) (cutSystem_smooth I R U hU hd)
    (cutSystem_closed I R U hU hd hc)

def cutMetric : RiemannianMetric 3 (cutCarrier I R U hU hd hc).carrier :=
  metric (cutSystem I R U hU hd) (cutSystem_smooth I R U hU hd)
    (cutSystem_closed I R U hU hd hc) (cutPieceMetric I R U)
    (cutSystem_metric I R U hU hd)

end PoincareConjecture.Surgery.Terminal.Gluing

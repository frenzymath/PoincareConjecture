import PoincareConjecture.Proofs.Horizon.Topology.Gluing.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.InnerProductSpace.PiL2









noncomputable section
set_option autoImplicit false

open Set Topology
open scoped Manifold

universe u v

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} {P : ι → Type v} [∀ i, TopologicalSpace (P i)]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
  (O : Poincare.Gluing.OverlapSystem P)

def liftedChart (a : Sigma P) :
    OpenPartialHomeomorph (Quotient O.setoid) (EuclideanSpace ℝ (Fin 3)) :=
  (chartAt (EuclideanSpace ℝ (Fin 3)) a.2).lift_openEmbedding (O.include_isOpenEmbedding a.1)

theorem liftedChart_apply (a : Sigma P) (x : P a.1) :
    liftedChart O a (O.include a.1 x) = chartAt (EuclideanSpace ℝ (Fin 3)) a.2 x :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _

theorem liftedChart_source (a : Sigma P) :
    (liftedChart O a).source =
      O.include a.1 '' (chartAt (EuclideanSpace ℝ (Fin 3)) a.2).source := rfl

theorem liftedChart_target (a : Sigma P) :
    (liftedChart O a).target = (chartAt (EuclideanSpace ℝ (Fin 3)) a.2).target := rfl

theorem liftedChart_symm (a : Sigma P) (x : EuclideanSpace ℝ (Fin 3)) :
    (liftedChart O a).symm x =
      O.include a.1 ((chartAt (EuclideanSpace ℝ (Fin 3)) a.2).symm x) := rfl

theorem liftedChart_transition (a b : Sigma P) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ((liftedChart O a).symm.trans (liftedChart O b)).source) :
    let y := (chartAt (EuclideanSpace ℝ (Fin 3)) a.2).symm x
    y ∈ (O.transition a.1 b.1).source ∧
      O.transition a.1 b.1 y ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) b.2).source ∧
      ((liftedChart O a).symm.trans (liftedChart O b)) x =
        chartAt (EuclideanSpace ℝ (Fin 3)) b.2 (O.transition a.1 b.1 y) := by
  change x ∈ (liftedChart O a).target ∧
    (liftedChart O a).symm x ∈ (liftedChart O b).source at hx
  rw [liftedChart_source] at hx
  obtain ⟨z, hz, heq⟩ := hx.2
  have hrel := (O.include_eq_iff a.1 b.1
    ((chartAt (EuclideanSpace ℝ (Fin 3)) a.2).symm x) z).mp heq.symm
  refine ⟨hrel.1, hrel.2.symm ▸ hz, ?_⟩
  change liftedChart O b ((liftedChart O a).symm x) = _
  rw [← heq, liftedChart_apply, hrel.2]

theorem liftedChart_cover (q : Quotient O.setoid) :
    ∃ a : Sigma P, q ∈ (liftedChart O a).source := by
  induction q using Quotient.inductionOn with
  | h a => exact ⟨a, a.2, mem_chart_source _ a.2, rfl⟩

@[implicit_reducible]
def chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Quotient O.setoid) where
  atlas := range (liftedChart O)
  chartAt q := liftedChart O (Classical.choose (liftedChart_cover O q))
  mem_chart_source q := Classical.choose_spec (liftedChart_cover O q)
  chart_mem_atlas _ := ⟨_, rfl⟩

end PoincareConjecture.Surgery.Terminal.Gluing

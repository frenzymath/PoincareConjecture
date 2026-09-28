import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeActionLimit










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



structure GaugePrimitivePartition (gamma : ℝ → G.Point) (a b : ℝ) where
  count : ℕ
  node : Fin (count + 1) → ℝ
  monotone : Monotone node
  first : node 0 = a
  last : node (Fin.last count) = b
  gauge : Fin count → AttainmentGauge G
  left : Fin count → ℝ
  right : Fin count → ℝ
  big_subset : ∀ i, Icc (left i) (right i) ⊆ Icc a b
  core_subset : ∀ i, Icc (node i.castSucc) (node i.succ) ⊆ Icc (left i) (right i)
  near : ∀ i s, s ∈ Icc (node i.castSucc) (node i.succ) →
    Icc (left i) (right i) ∈ 𝓝[Icc a b] s
  source : ∀ i, MapsTo gamma (Icc (left i) (right i)) (gauge i).source
  velocity : ∀ i : Fin count,
    M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (node i.castSucc) (node i.succ)
  primitive : ∀ i s, s ∈ Icc (node i.castSucc) (node i.succ) →
    ((gauge i).lift (gamma s)).2.val = ((gauge i).lift (gamma (node i.castSucc))).2.val +
      ∫ r in node i.castSucc..s, velocity i r




noncomputable def GaugePrimitivePartition.action {gamma : ℝ → G.Point} {a b : ℝ}
    (R : GaugePrimitivePartition gamma a b) : ℝ :=
  ∑ i, gaugePieceAction (R.gauge i) gamma (R.velocity i)

end PoincareConjecture.Proofs.M46

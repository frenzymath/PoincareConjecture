import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteDistanceDyadic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    T3Space L.carrier.carrier := L.carrier.t3Space
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ConnectedSpace L.carrier.carrier := L.connectedSpace



theorem limitFinite_compact_diameter (h04 : RicciFlowCurvatureTheory.{u})
    {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) {B0 : ℝ}
    (hterminal : ∀ x : L.carrier.carrier,
      (L.flow.connection 0).curvatureTensorNorm x ≤ B0)
    {X : Set L.carrier.carrier} (hX : IsCompact X) :
    ∃ DX : ℝ, 1 ≤ DX ∧ ∀ t ∈ blowupBackwardInterval H,
      ∀ x ∈ X, ∀ y ∈ X, ((L.flow.metric t).edist x y).toReal ≤ DX := by
  let g := L.flow.metric 0
  obtain ⟨b, hb⟩ := (hX.image (g.continuous_toReal_edist L.base)).bddAbove
  let DX := max 1 (2 * max b 0 + 80 * H.toReal * Real.sqrt (max 1 (3 * B0)))
  refine ⟨DX, le_max_left _ _, ?_⟩
  intro t ht x hx y hy
  have hx0 : (g.edist L.base x).toReal ≤ max b 0 :=
    (hb ⟨x, hx, rfl⟩).trans (le_max_left _ _)
  have hy0 : (g.edist L.base y).toReal ≤ max b 0 :=
    (hb ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  have hcomm : g.edist x L.base = g.edist L.base x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : L.carrier.carrier → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_comm
  have hxy := g.toReal_edist_triangle x L.base y
  rw [hcomm] at hxy
  have hdist := (limitFinite_additive_distance h04 hH hfinite L hterminal t ht x y).2
  apply hdist.trans
  apply le_trans _ (le_max_right _ _)
  change (g.edist x y).toReal + _ ≤ _
  linarith

end PoincareConjecture.M47

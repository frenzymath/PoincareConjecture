import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialLineKernel
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeParameterDifferential









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem projected_horizontal_heq {q r : G.Point} (h : q = r)
    {v : TangentSpace (spacetimeModel n) q} {w : G.Horizontal r} (hv : HEq v w.val) :
    HEq (G.spacetime.horizontalProjection q v) w := by
  cases h
  rw [eq_of_heq hv, G.spacetime.horizontalProjection_identity]




theorem exponentialLine_differential_gauge (E : M14ExponentialFamily G T x)
    (Z W : G.Horizontal x) {s : ℝ} (hs : (Z, s) ∈ E.domain) (j : G.gaugeCover.index)
    (β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point × G.gaugeCover.spatial j)
    (hβ : MDifferentiableAt (𝓘(ℝ, ℝ)) (spacetimeModel n) β 0)
    (hrec : (fun r : ℝ => E.gamma (Z + r • W) s) =ᶠ[𝓝 0]
      (fun r => (G.gaugeCover.cylinder j).toSpacetime (β r))) :
    HEq (E.differential Z s hs W) ((G.gaugeCover.metric j).spatialTangentEquiv
      (β 0).1 (β 0).2 (fderiv ℝ (fun r => (β r).2.val) 0 (1 : ℝ))) := by
  have hgauge := gaugeMap_projectedDifferential_congr j hβ hrec (1 : ℝ)
  have hpoint : E.gamma (Z + (0 : ℝ) • W) s = E.gamma Z s := by simp only [zero_smul, add_zero]
  have hproject := projected_horizontal_heq hpoint (heq_of_eq (exponentialLine_mfderiv E Z W hs))
  exact hproject.symm.trans hgauge

end PoincareConjecture.M14

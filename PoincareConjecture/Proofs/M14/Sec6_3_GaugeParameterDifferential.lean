import PoincareConjecture.Proofs.M14.Sec6_4_GaugeVelocity










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {β : E → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b} {z : E}




theorem gaugeMap_projectedDifferential
    (hβ : MDifferentiableAt (𝓘(ℝ, E)) (spacetimeModel n) β z) (v : E) :
    G.spacetime.horizontalProjection ((G.gaugeCover.cylinder b).toSpacetime (β z))
      (mfderiv (𝓘(ℝ, E)) (spacetimeModel n)
        (fun y => (G.gaugeCover.cylinder b).toSpacetime (β y)) z v) =
      (G.gaugeCover.metric b).spatialTangentEquiv (β z).1 (β z).2
        (fderiv ℝ (fun y => (β y).2.val) z v) := by
  have hd := mfderiv_comp_apply z
    ((G.gaugeCover.cylinder b).smooth.mdifferentiableAt (by simp)) hβ v
  have hsp := congrArg (fun L => (L v).2) (mfderiv_prodMk hβ.fst hβ.snd)
  change (mfderiv (𝓘(ℝ, E)) (spacetimeModel n) β z v).2 =
    mfderiv (𝓘(ℝ, E)) (𝓡 n) (fun y => (β y).2) z v at hsp
  have hi : MDifferentiableAt (𝓡 n) (𝓡 n)
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) (β z).2 :=
    contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
  have hv := mfderiv_comp_apply z hi hβ.snd v
  rw [Proofs.M11.mfderiv_openSubtype_val, mfderiv_eq_fderiv] at hv
  change fderiv ℝ (fun y => (β y).2.val) z v =
    mfderiv (𝓘(ℝ, E)) (𝓡 n) (fun y => (β y).2) z v at hv
  dsimp only [Function.comp_def] at hd
  rw [hd, gauge_projectedDifferential b, hsp, ← hv]

private theorem projected_tangent_heq {q r : G.Point} (h : q = r)
    {v : TangentSpace (spacetimeModel n) q} {w : TangentSpace (spacetimeModel n) r}
    (hv : HEq v w) :
    HEq (G.spacetime.horizontalProjection q v) (G.spacetime.horizontalProjection r w) := by
  cases h
  cases hv
  rfl




theorem gaugeMap_projectedDifferential_congr {γ : E → G.Point}
    (hβ : MDifferentiableAt (𝓘(ℝ, E)) (spacetimeModel n) β z)
    (hrec : γ =ᶠ[𝓝 z] fun y => (G.gaugeCover.cylinder b).toSpacetime (β y)) (v : E) :
    HEq (G.spacetime.horizontalProjection (γ z)
      (mfderiv (𝓘(ℝ, E)) (spacetimeModel n) γ z v))
      ((G.gaugeCover.metric b).spatialTangentEquiv (β z).1 (β z).2
        (fderiv ℝ (fun y => (β y).2.val) z v)) := by
  have hd := congrArg (fun L : E →L[ℝ] SpacetimeModelVector n => L v)
    (hrec.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := spacetimeModel n))
  exact (projected_tangent_heq hrec.eq_of_nhds (heq_of_eq hd)).trans
    (heq_of_eq (gaugeMap_projectedDifferential b hβ v))

end PoincareConjecture.M14

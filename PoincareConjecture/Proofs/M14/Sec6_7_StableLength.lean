import PoincareConjecture.Proofs.M14.Sec6_3_StableSliceChart
import PoincareConjecture.Proofs.M14.Sec6_3_StablePrefix
import PoincareConjecture.Proofs.M14.Sec6_3_ActionSmooth
import Mathlib.Geometry.Manifold.Algebra.LieGroup










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}



theorem reducedLengthValue_stableEndpoint_eq_action (H : M14StableSet G T τ x E)
    {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    M14ReducedLengthValue G T 0 τ x (H.endpoint_slice_map Z).val =
      E.action Z (Real.sqrt τ) / (2 * Real.sqrt τ) := by
  have hs := Real.sqrt_pos.mpr H.tau_pos
  have hbranch : M14UniqueMinimizingBranch G T ((Real.sqrt τ) ^ 2) x E Z := by
    simpa only [Real.sq_sqrt H.tau_pos.le] using
      stableInitialVector_unique_branch E ((H.carrier_exact Z).mp hZ)
  have hmin := exponentialPath_minimizing_of_uniqueBranch E hs (H.survivor Z hZ) hbranch
  have hglobal := E.reduced_length_global_eq Z (Real.sqrt τ) (H.survivor Z hZ) hs hmin
  rw [Real.sq_sqrt H.tau_pos.le] at hglobal
  rw [H.endpoint_slice_map_val Z hZ, H.endpoint_map_eq Z hZ, ← hglobal]
  exact E.reduced_length_eq Z (Real.sqrt τ) (H.survivor Z hZ) hs




theorem stable_normalizedAction_smooth
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) :
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
    ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (𝓘(ℝ, ℝ)) ∞
      (fun Z => E.action Z (Real.sqrt τ) / (2 * Real.sqrt τ)) H.carrier := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have ha := (exponentialFamily_action_smooth hM04 hM12 E).comp
    (contMDiff_id.prodMk (contMDiff_const (c := Real.sqrt τ))).contMDiffOn
    (fun Z hZ => ⟨H.survivor Z hZ, Real.sqrt_pos.mpr H.tau_pos⟩)
  exact ha.div₀ (contMDiffOn_const (c := 2 * Real.sqrt τ))
    (fun _ _ => (mul_pos zero_lt_two (Real.sqrt_pos.mpr H.tau_pos)).ne')




theorem reducedLengthValue_contMDiffOn_stableImage
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (H : M14StableSet G T τ x E) :
    ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞
      (fun q : (G.slices (T - τ)).Point => M14ReducedLengthValue G T 0 τ x q.val)
      (H.endpoint_slice_map '' H.carrier) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  let e := stableSliceChart H
  have h := (stable_normalizedAction_smooth hM04 hM12 H).comp
    (stableSliceChart_symm_smooth H) (fun q hq => e.map_target hq)
  apply h.congr
  intro q hq
  have heq : H.endpoint_slice_map (e.symm q) = q := e.right_inv hq
  exact (congrArg (fun r : (G.slices (T - τ)).Point =>
    M14ReducedLengthValue G T 0 τ x r.val) heq).symm.trans
      (reducedLengthValue_stableEndpoint_eq_action H (e.map_target hq))

end PoincareConjecture.M14

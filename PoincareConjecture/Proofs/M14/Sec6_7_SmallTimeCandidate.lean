import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeCandidateTube
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeCandidateSpeed
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeCandidateAction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem smallTimeCandidateBounds (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {B : Set (G.Horizontal x)} (hB : IsCompact B)
    (b : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b)
    {O : Set G.Point} (hO : IsOpen O) (hxO : x ∈ O)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift O)
    {δ : ℝ} (hδ : 0 < δ) (hwindow : Icc (T - δ) T ⊆ I.domain) :
    ∃ (N : Set (G.Horizontal x)) (η M A : ℝ), IsOpen N ∧ B ⊆ N ∧
      0 < η ∧ η ≤ δ ∧ 0 ≤ M ∧ 0 ≤ A ∧
      (∀ W ∈ N, ∀ σ ∈ Icc 0 η,
        (W, Real.sqrt σ) ∈ E.domain ∧ E.gamma W (Real.sqrt σ) ∈ O) ∧
      (∀ W ∈ N, ∀ (τ : ℝ) (hτ : τ ∈ Ioc 0 η)
        (hD : (W, Real.sqrt τ) ∈ E.domain), ∀ r ∈ Icc 0 (Real.sqrt τ),
          ‖derivWithin
            (fun v => (lift ((E.path W (Real.sqrt τ) hD (Real.sqrt_pos.mpr hτ.1)).curve
              (v ^ 2))).2.val) (Icc 0 (Real.sqrt τ)) r‖ ≤ M) ∧
      (∀ W ∈ N, ∀ (τ : ℝ) (hτ : τ ∈ Ioc 0 η)
        (hD : (W, Real.sqrt τ) ∈ E.domain),
          M14BackwardLAction G (E.path W (Real.sqrt τ) hD (Real.sqrt_pos.mpr hτ.1)) ≤
            A * Real.sqrt τ) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  obtain ⟨N, K, U, hN, hBN, hNK, hK, hKU, hU, η, hη, hηδ, hcapture⟩ :=
    exists_smallTimeCandidate_tube E hB hO hxO hδ hwindow
  obtain ⟨hcoord, M, hM, hspeed⟩ := exists_smallTimeCandidate_coordinate_bound E b lift
    hU hK hKU hlift hη hcapture
  obtain ⟨A, hA, hdensity⟩ := exists_smallTimeCandidate_density_bound hM12 E
    hU hK hKU hη hcapture
  obtain ⟨hγ, hmap⟩ := smallTimeCandidate_family_smooth E hη.le hcapture
  refine ⟨N, η, M, A, hN, hBN, hη, hηδ, hM, hA,
    fun W hW => hcapture W (hKU (hNK hW)), ?_, ?_⟩
  · intro W hW τ hτ hD
    have hCW : ContDiffOn ℝ ∞ (fun r => (lift (E.gamma W r)).2.val)
        (Icc 0 (Real.sqrt η)) :=
      hcoord.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun _ hr => ⟨hr, hKU (hNK hW)⟩)
    exact smallTimeCandidate_coordinate_speed_le E b lift W (Real.sqrt_pos.mpr hτ.1)
      (Real.sqrt_le_sqrt hτ.2) hD hCW (hspeed W (hNK hW))
  · intro W hW τ hτ hD
    have hγW : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (E.gamma W)
        (Icc 0 (Real.sqrt η)) :=
      hγ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
        (fun _ hr => ⟨hr, hKU (hNK hW)⟩)
    exact smallTimeCandidate_action_le hM12 E W (Real.sqrt_pos.mpr hτ.1)
      (Real.sqrt_le_sqrt hτ.2) hD hγW
      (fun r hr => (hmap W (hKU (hNK hW)) r hr).1) (hdensity W (hNK hW))

end PoincareConjecture.M14

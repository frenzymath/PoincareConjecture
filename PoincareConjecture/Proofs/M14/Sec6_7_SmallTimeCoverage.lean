import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeUniqueBranches
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeCandidate
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeStability
import PoincareConjecture.Proofs.M14.Mathlib.CompactCoordinateBox
import PoincareConjecture.Statements.M14GeneralizedLGeometry

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem exists_open_smallTime_uniqueMinimizing
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (E : M14ExponentialFamily G T x)
    {B : Set (G.Horizontal x)} (hB : IsCompact B)
    {δ : ℝ} (hδ : 0 < δ) (hwindow : Icc (T - δ) T ⊆ I.domain)
    {C : ℝ} (hC : 0 ≤ C)
    (hcurv : ∀ q : G.Point, G.spacetime.timeFunction q ∈ Icc (T - δ) T →
      horizontalCurvatureNorm G.leafwise q ≤ C) :
    ∃ N : Set (G.Horizontal x), IsOpen N ∧ B ⊆ N ∧
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧
        ∀ W ∈ N, ∀ τ ∈ Ioc 0 ε, M14UniqueMinimizingBranch G T τ x E W := by
  obtain ⟨b, U, lift, hU, hxU, hlift, hright, htime⟩ := exists_smooth_gauge_lift G x
  have hcoord_cont : ContinuousOn (fun q => (lift q).2.val) U :=
    continuous_subtype_val.comp_continuousOn hlift.continuousOn.snd
  obtain ⟨O, hO, hxO, hOU, S, hS, hconvex, hSU, hcoord⟩ :=
    exists_compact_convex_coordinate_box hU hxU (fun q => (lift q).2.val) hcoord_cont
      (G.gaugeCover.spatial b).isOpen (lift x).2.property
  obtain ⟨N, η, M, A, hN, hBN, hη, hηδ, _hM, hA, hcapture, hspeed, haction⟩ :=
    smallTimeCandidateBounds hM12 E (hB.insert 0) b lift hO hxO
      (hlift.mono hOU) hδ hwindow
  obtain ⟨ε, hε, hεη, hunique⟩ :=
    exists_uniform_uniqueMinimizing_of_candidate_bounds hCoordinates hM12 E b lift
      hU hlift hright htime hO hxO hOU hS hconvex hSU hcoord
      (hBN (mem_insert 0 B)) hη hηδ hA hC hcurv hcapture hspeed haction
  exact ⟨N, hN, (subset_insert 0 B).trans hBN, ε, hε, hεη.trans hηδ, hunique⟩

theorem smallTimeCoverageStatement (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (G : GeneralizedLGeometryTransport n X time I) : M14SmallTimeCoverageStatement G := by
  intro T x E B K δ hδ hwindow hB _hK hKN _hR hcurv
  obtain ⟨C, hC, hcurv⟩ := hcurv
  obtain ⟨N, hN, hBN, η, hη, hηδ, hunique⟩ :=
    exists_open_smallTime_uniqueMinimizing hCoordinates hM12 E hB hδ hwindow hC hcurv
  exact smallTime_stability_of_open_uniqueMinimizing E hB hKN hδ hwindow
    hN hBN hη hηδ hunique

end PoincareConjecture.M14

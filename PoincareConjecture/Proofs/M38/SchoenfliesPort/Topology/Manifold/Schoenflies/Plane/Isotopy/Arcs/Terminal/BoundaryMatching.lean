import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualBoundaryCircles







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs
open _root_.Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem exists_terminal_boundary_matching_equiv
    (d : TerminalSaddleGeometry M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦi : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (hplanar : ∀ z ∈ d.I, Φ 1 z '' d.A z = d.B z)
    (B : Fin 3 → S1 → E3) (hB : ∀ i, Continuous (B i))
    (hBdis : Pairwise (fun i j => Disjoint (range (B i)) (range (B j))))
    (hBunion : (⋃ i, range (B i)) =
      Saddle.slice (d.B d.ends.lowerCut) d.ends.lowerCut ∪
      Saddle.slice (d.B d.ends.upperCut) d.ends.upperCut) :
    ∃ E : Fin 3 ≃ Fin 3, ∀ i,
      planarHeightMap Φ 1 '' (d.C i ∩ d.actualBand) = range (B (E i)) := by
  have hforward : ContDiff Real ∞ (fun q : Real × E2 => Φ 1 q.1 q.2) :=
    hΦ.comp (contDiff_const.prodMk contDiff_id)
  have hinverse : ContDiff Real ∞ (fun q : Real × E2 => (Φ 1 q.1).symm q.2) :=
    hΦi.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨H, hH, _, _, hslice⟩ := Saddle.exists_height_lift (Φ 1) hforward hinverse
  have hHeq : (H : E3 → E3) = planarHeightMap Φ 1 := funext hH
  let A : Fin 3 → S1 → E3 := fun i => H ∘ terminalActualBoundaryCircle d i
  have hA (i) : Continuous (A i) :=
    H.contMDiff.continuous.comp (terminalActualBoundaryCircle_continuous d hg i)
  have hr (i) : range (A i) = H '' range (terminalActualBoundaryCircle d i) :=
    range_comp _ _
  have hAdis : Pairwise (fun i j => Disjoint (range (A i)) (range (A j))) := by
    intro i j hij
    rw [hr i, hr j]
    exact (terminalActualBoundaryCircle_pairwise_disjoint d hij).image
      H.injective.injOn (subset_univ _) (subset_univ _)
  have hunion : (⋃ i, range (A i)) = ⋃ i, range (B i) := by
    simp_rw [hr]
    rw [← image_iUnion, iUnion_range_terminalActualBoundaryCircle, image_union,
      hslice, hslice,
      hplanar d.ends.lowerCut ⟨le_rfl, d.ends.cuts_lt.le⟩,
      hplanar d.ends.upperCut ⟨d.ends.cuts_lt.le, le_rfl⟩]
    exact hBunion.symm
  obtain ⟨E, hE⟩ := exists_finite_circle_range_equiv A B hA hB hAdis hBdis hunion
  refine ⟨E, fun i => ?_⟩
  rw [← range_terminalActualBoundaryCircle d hg i, ← hHeq, ← hr i]
  exact hE i

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies

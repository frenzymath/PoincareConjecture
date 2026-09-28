import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.BoundaryMatching
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelBoundaryCircles
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelDataAssembly

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
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_labeled_terminal_data_of_planar_family
    (d : TerminalSaddleGeometry M P p e) (hg : g ∈ M.tree.leaves)
    (a : ModelCutCircleData d d.eta) (b : ModelCutDiskData d d.eta a)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦi : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (hplanar : ∀ z ∈ d.I, Φ 1 z '' d.A z = d.B z) :
    ∃ E : Fin 3 ≃ Fin 3,
      ∃ hseed : ∀ i, inner Real (M.v : E3) (d.filledModel (b.seed (E i))) ∉ d.I,
      ∃ data : TerminalSaddleData M P p e,
        data.toTerminalSaddleGeometry = d.withModelSeeds (b.seed ∘ E) hseed ∧
        data.modelDisk = b.chart ∘ E ∧
        ∀ i, planarHeightMap Φ 1 ''
          (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
          data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand := by
  obtain ⟨E, hE⟩ := exists_terminal_boundary_matching_equiv d hg Φ hΦ hΦi hplanar
    (terminalModelBoundaryCircle d a) (terminalModelBoundaryCircle_continuous d a)
    (terminalModelBoundaryCircle_pairwise_disjoint d a b)
    (iUnion_range_terminalModelBoundaryCircle d a)
  have hseed₀ (i : Fin 3) : inner Real (M.v : E3) (d.filledModel (b.seed i)) ∉ d.I := by
    change inner Real (M.v : E3) (d.filledModel (b.seed i)) ∉
      Icc d.ends.lowerCut d.ends.upperCut
    rw [d.lowerCut_eq, d.upperCut_eq]
    intro hi
    fin_cases i
    · exact (b.seed_lower 0).not_ge hi.1
    · exact (b.seed_lower 1).not_ge hi.1
    · exact b.seed_upper.not_ge hi.2
  let hseed := fun i => hseed₀ (E i)
  have hopen (i) : (b.chart ∘ E) i '' ball 0 1 = connectedComponentIn
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉ d.I} ((b.seed ∘ E) i) := by
    simpa only [TerminalSaddleGeometry.I, d.lowerCut_eq, d.upperCut_eq, comp_apply]
      using b.open_component (E i)
  have hdis : Pairwise (fun i j => Disjoint
      ((b.chart ∘ E) i '' closedBall 0 1) ((b.chart ∘ E) j '' closedBall 0 1)) := by
    intro i j hij
    exact b.disjoint (E i) (E j) (E.injective.ne hij)
  have hcover : (⋃ i, (b.chart ∘ E) i '' ball 0 1) =
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉ d.I} := by
    rw [show (⋃ i, (b.chart ∘ E) i '' ball 0 1) = ⋃ j, b.chart j '' ball 0 1 from
      E.surjective.iUnion_comp (fun j => b.chart j '' ball 0 1)]
    simpa only [TerminalSaddleGeometry.I, d.lowerCut_eq, d.upperCut_eq] using b.cover
  obtain ⟨data, hgeom, hdisk⟩ := exists_terminal_data_of_model_component_disks d hg
    (b.seed ∘ E) hseed (b.chart ∘ E) (fun i => b.source (E i))
    (fun i => b.smooth (E i)) (fun i => b.inverse_smooth (E i)) hopen hdis hcover
  refine ⟨E, hseed, data, hgeom, hdisk, fun i => ?_⟩
  rw [data.model_boundary i, hgeom, hdisk]
  exact (hE i).trans (range_terminalModelBoundaryCircle d a b (E i))

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies

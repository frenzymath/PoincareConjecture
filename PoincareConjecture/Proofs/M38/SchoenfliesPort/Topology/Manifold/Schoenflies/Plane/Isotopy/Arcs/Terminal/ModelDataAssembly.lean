import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelBoundary
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ActualEndDisjoint

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
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

def _root_.M38Schoenflies.Poincare.Manifold.Schoenflies.SaddleLevel.TerminalSaddleGeometry.withModelSeeds
    (d : TerminalSaddleGeometry M P p e) (seed : Fin 3 → S2)
    (hseed : ∀ i, inner Real (M.v : E3) (d.filledModel (seed i)) ∉ d.I) :
    TerminalSaddleGeometry M P p e :=
  { d with modelSeed := seed, modelSeed_outside := hseed }

theorem exists_terminal_data_of_model_component_disks
    (d : TerminalSaddleGeometry M P p e) (hg : g ∈ M.tree.leaves)
    (seed : Fin 3 → S2)
    (hseed : ∀ i, inner Real (M.v : E3) (d.filledModel (seed i)) ∉ d.I)
    (m : Fin 3 → OpenPartialHomeomorph E2 S2)
    (hs : ∀ i, closedBall 0 1 ⊆ (m i).source)
    (hms : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (m i) (m i).source)
    (hmi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (m i).symm (m i).target)
    (hopen : ∀ i, m i '' ball 0 1 = connectedComponentIn
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉ d.I} (seed i))
    (hdis : Pairwise (fun i j =>
      Disjoint (m i '' closedBall 0 1) (m j '' closedBall 0 1)))
    (hcover : (⋃ i, m i '' ball 0 1) =
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉ d.I}) :
    ∃ data : TerminalSaddleData M P p e,
      data.toTerminalSaddleGeometry = d.withModelSeeds seed hseed ∧ data.modelDisk = m := by
  let d' := d.withModelSeeds seed hseed
  have hclosed (i : Fin 3) : m i '' closedBall 0 1 = d'.modelDomain i := by
    rw [← ParallelDisks.closure_image_ball zero_lt_one (m i) (hs i), hopen i]
    rfl
  have hboundary (i : Fin 3) : d'.modelCaps i ∩ d'.modelBand =
      (fun x => d'.flatten (d'.filledModel (m i x))) '' sphere (0 : E2) 1 :=
    terminal_model_cap_band_boundary d' i (m i) (hs i) (hms i) (hmi i) (hopen i)
  have hdecomp : d'.flatten '' (d'.filledModel '' sphere (0 : E3) 1) =
      d'.modelBand ∪ ⋃ i, d'.modelCaps i := by
    rw [terminal_modelBand_eq_image_height_band]
    apply Subset.antisymm
    · rintro y ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      let z : S2 := ⟨q, hq⟩
      by_cases hz : inner Real (M.v : E3) (d.filledModel z) ∈ d.I
      · exact Or.inl ⟨z, hz, rfl⟩
      · have hm : z ∈ ⋃ i, m i '' ball 0 1 := hcover.symm ▸ hz
        obtain ⟨i, hi⟩ := mem_iUnion.mp hm
        refine Or.inr (mem_iUnion_of_mem i ?_)
        exact ⟨z, hclosed i ▸ image_mono ball_subset_closedBall hi, rfl⟩
    · rintro y (⟨q, _, rfl⟩ | hy)
      · exact mem_image_of_mem _ (mem_image_of_mem _ q.property)
      · obtain ⟨i, q, _, rfl⟩ := by
          simpa only [mem_iUnion, TerminalSaddleGeometry.modelCaps, mem_image] using hy
        exact mem_image_of_mem _ (mem_image_of_mem _ q.property)
  have hdisjoint : Pairwise (fun i j => Disjoint (d'.modelCaps i) (d'.modelCaps j)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro y ⟨q, hq, rfl⟩ ⟨z, hz, heq⟩
    have hzq : z = q := Subtype.ext (d'.filledModel.injective (d'.flatten.injective heq))
    subst z
    exact disjoint_left.mp (hdis hij) (hclosed i ▸ hq) (hclosed j ▸ hz)
  obtain ⟨a, ha⟩ := exists_terminal_actual_disks_with_band_boundary d' hg
  refine ⟨{
    toTerminalSaddleGeometry := d'
    actualDisk := a
    actualDisk_source := fun i => (ha i).1
    actualDisk_smooth := fun i => (ha i).2.1
    actualDisk_symm_smooth := fun i => (ha i).2.2.1
    actualDisk_image := fun i => (ha i).2.2.2.1
    modelDisk := m
    modelDisk_source := hs
    modelDisk_smooth := hms
    modelDisk_symm_smooth := hmi
    modelDisk_image := hclosed
    actual_decomposition := terminal_actual_decomposition d'
    model_decomposition := hdecomp
    actual_boundary := fun i => (ha i).2.2.2.2
    model_boundary := hboundary
    actual_disjoint := terminal_actual_caps_pairwise_disjoint d'
    model_disjoint := hdisjoint }, rfl, rfl⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

end

end M38Schoenflies

import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open SaddleLevel

private theorem slice_union_eq_inter (S : Set E3) (I : Set Real) :
    (⋃ z ∈ I, Saddle.slice {x | Saddle.toE3 x z ∈ S} z) = S ∩ {y | y 2 ∈ I} := by
  have hcoord (y : E3) : Saddle.toE3 (Saddle.toE2 y) (y 2) = y := by
    ext i
    fin_cases i <;> rfl
  ext y
  simp only [mem_iUnion, Saddle.slice, mem_ofPred_eq, mem_inter_iff]
  constructor
  · rintro ⟨z, hz, hy, heq⟩
    subst z
    exact ⟨hcoord y ▸ hy, hz⟩
  · rintro ⟨hy, hz⟩
    exact ⟨y 2, hz, hcoord y ▸ hy, rfl⟩

private theorem disk_interior_disjoint_of_boundary
    {a : E2 → E3} (ha : InjOn a (closedBall 0 1)) {C W : Set E3}
    (hC : a '' closedBall 0 1 = C)
    (hboundary : C ∩ W = a '' sphere (0 : E2) 1) :
    Disjoint (a '' ball (0 : E2) 1) W := by
  apply disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ hxW
  have hxC : a x ∈ C := hC ▸ mem_image_of_mem a (ball_subset_closedBall hx)
  obtain ⟨y, hy, hyx⟩ := hboundary ▸ (show a x ∈ C ∩ W from ⟨hxC, hxW⟩)
  have heq := ha (sphere_subset_closedBall hy) (ball_subset_closedBall hx) hyx
  subst y
  exact (ne_of_lt (mem_ball.mp hx)) (mem_sphere.mp hy)

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem isCompact_terminal_modelBand (data : TerminalSaddleData M P p e) :
    IsCompact data.toTerminalSaddleGeometry.modelBand := by
  unfold TerminalSaddleGeometry.modelBand TerminalSaddleGeometry.B
  rw [slice_union_eq_inter]
  apply ((isCompact_sphere (0 : E3) 1).image
    data.toTerminalSaddleGeometry.filledModel.contMDiff.continuous).image
      data.toTerminalSaddleGeometry.flatten.contMDiff.continuous |>.inter_right
  exact isClosed_Icc.preimage (EuclideanSpace.proj 2).continuous

theorem actual_terminal_cap_interior_disjoint_band
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves) (i : Fin 3) :
    Disjoint ((data.toTerminalSaddleGeometry.flatten ∘ g ∘ data.actualDisk i) ''
      ball (0 : E2) 1) data.toTerminalSaddleGeometry.actualBand := by
  refine disk_interior_disjoint_of_boundary
    (C := data.toTerminalSaddleGeometry.C i) ?_ ?_ (data.actual_boundary i)
  · intro x hx y hy hxy
    exact (data.actualDisk i).injOn (data.actualDisk_source i hx)
      (data.actualDisk_source i hy)
      ((M.tree.embedding_of_mem_leaves hg).isEmbedding.injective
        (data.toTerminalSaddleGeometry.flatten.injective hxy))
  · simp only [image_comp, data.actualDisk_image, TerminalSaddleGeometry.C]

theorem model_terminal_cap_interior_disjoint_band
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    Disjoint ((fun x => data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x))) ''
        ball (0 : E2) 1) data.toTerminalSaddleGeometry.modelBand := by
  refine disk_interior_disjoint_of_boundary
    (C := data.toTerminalSaddleGeometry.modelCaps i) ?_ ?_ (data.model_boundary i)
  · intro x hx y hy hxy
    exact (data.modelDisk i).injOn (data.modelDisk_source i hx)
      (data.modelDisk_source i hy)
      (Subtype.val_injective (data.toTerminalSaddleGeometry.filledModel.injective
        (data.toTerminalSaddleGeometry.flatten.injective hxy)))
  · change (fun q : S2 => data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel q)) ∘ data.modelDisk i '' closedBall 0 1 = _
    rw [image_comp, data.modelDisk_image]
    rfl

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies

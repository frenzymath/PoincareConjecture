import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.TerminalObstacles
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

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

private theorem exists_outer_annulus_of_sphere_disk_family
    {ι : Type*} [Finite ι]
    (s : S2 → E3) (hs : Continuous s) (hsi : Injective s)
    (m : ι → OpenPartialHomeomorph E2 S2)
    (hsource : ∀ i, closedBall 0 1 ⊆ (m i).source)
    (hm : ∀ i, ContinuousOn (m i) (m i).source)
    (band : Set E3) (C : ι → Set E3)
    (hcap : ∀ i, (s ∘ m i) '' closedBall 0 1 = C i)
    (hdecomp : range s = band ∪ ⋃ i, C i)
    (hboundary : ∀ i, (s ∘ m i) '' sphere (0 : E2) 1 ⊆ band)
    (hdis : Pairwise (fun i j => Disjoint (C i) (C j))) (i : ι) :
    ∃ r : Real, 1 < r ∧ closedBall 0 r ⊆ (m i).source ∧
      (s ∘ m i) '' (closedBall (0 : E2) r \ ball 0 1) ⊆ band := by
  classical
  have hclosed (j : ι) : IsClosed (C j) := by
    rw [← hcap j]
    exact ((isCompact_closedBall (0 : E2) 1).image_of_continuousOn
      ((hs.comp_continuousOn (hm j)).mono (hsource j))).isClosed
  let D : Set E3 := ⋃ j : {j : ι // j ≠ i}, C j
  have hD : IsClosed D := isClosed_iUnion_of_finite (fun j => hclosed j)
  let V : Set E2 := (m i).source ∩ (s ∘ m i) ⁻¹' Dᶜ
  have hV : IsOpen V := (hs.comp_continuousOn (hm i)).isOpen_inter_preimage
    (m i).open_source hD.isOpen_compl
  have hunit : closedBall (0 : E2) 1 ⊆ V := by
    intro x hx
    refine ⟨hsource i hx, ?_⟩
    intro hxD
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxD
    exact disjoint_left.mp (hdis (Ne.symm j.property))
      (hcap i ▸ mem_image_of_mem (s ∘ m i) hx) hj
  obtain ⟨δ, hδ, hδV⟩ := (isCompact_closedBall (0 : E2) 1).exists_cthickening_subset_open
    hV hunit
  rw [cthickening_closedBall hδ.le (by norm_num : (0 : Real) ≤ 1)] at hδV
  refine ⟨δ + 1, by linarith, hδV.trans inter_subset_left, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hxV := hδV hx.1
  have hxS : (s ∘ m i) x ∈ range s := ⟨m i x, rfl⟩
  rw [hdecomp] at hxS
  rcases hxS with hxband | hxcap
  · exact hxband
  · obtain ⟨j, hj⟩ := mem_iUnion.mp hxcap
    have hji : j = i := by
      by_contra hji
      exact hxV.2 (mem_iUnion_of_mem ⟨j, hji⟩ hj)
    subst j
    obtain ⟨z, hz, hzx⟩ := (hcap i).symm ▸ hj
    have hzx' : z = x := (m i).injOn (hsource i hz) hxV.1 (hsi hzx)
    have hxsphere : x ∈ sphere (0 : E2) 1 := by
      rw [← closedBall_sdiff_ball]
      exact ⟨hzx' ▸ hz, hx.2⟩
    exact hboundary i (mem_image_of_mem (s ∘ m i) hxsphere)

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_actual_terminal_outer_annulus
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves) (i : Fin 3) :
    ∃ r : Real, 1 < r ∧ closedBall 0 r ⊆ (data.actualDisk i).source ∧
      (data.toTerminalSaddleGeometry.flatten ∘ g ∘ data.actualDisk i) ''
        (closedBall (0 : E2) r \ ball 0 1) ⊆ data.toTerminalSaddleGeometry.actualBand := by
  let s : S2 → E3 := data.toTerminalSaddleGeometry.flatten ∘ g
  have hs : Continuous s := data.toTerminalSaddleGeometry.flatten.continuous.comp
    (M.tree.embedding_of_mem_leaves hg).contMDiff.continuous
  have hsi : Injective s := data.toTerminalSaddleGeometry.flatten.injective.comp
    (M.tree.embedding_of_mem_leaves hg).isEmbedding.injective
  apply exists_outer_annulus_of_sphere_disk_family s hs hsi data.actualDisk
    data.actualDisk_source (fun j => (data.actualDisk_smooth j).continuousOn)
    data.toTerminalSaddleGeometry.actualBand data.toTerminalSaddleGeometry.C
    ?_ ?_ ?_ data.actual_disjoint i
  · intro j
    simp only [s, image_comp, data.actualDisk_image, TerminalSaddleGeometry.C]
  · change range (data.toTerminalSaddleGeometry.flatten ∘ g) = _
    rw [range_comp, data.actual_decomposition]
  · intro j
    change (data.toTerminalSaddleGeometry.flatten ∘ g ∘ data.actualDisk j) ''
      sphere (0 : E2) 1 ⊆ _
    rw [← data.actual_boundary j]
    exact inter_subset_right

theorem exists_model_terminal_outer_annulus
    (data : TerminalSaddleData M P p e) (i : Fin 3) :
    ∃ r : Real, 1 < r ∧ closedBall 0 r ⊆ (data.modelDisk i).source ∧
      (fun x => data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x))) ''
          (closedBall (0 : E2) r \ ball 0 1) ⊆ data.toTerminalSaddleGeometry.modelBand := by
  let s : S2 → E3 := fun q => data.toTerminalSaddleGeometry.flatten
    (data.toTerminalSaddleGeometry.filledModel q)
  have hs : Continuous s := data.toTerminalSaddleGeometry.flatten.continuous.comp
    (data.toTerminalSaddleGeometry.filledModel.continuous.comp continuous_subtype_val)
  have hsi : Injective s := data.toTerminalSaddleGeometry.flatten.injective.comp
    (data.toTerminalSaddleGeometry.filledModel.injective.comp Subtype.val_injective)
  apply exists_outer_annulus_of_sphere_disk_family s hs hsi data.modelDisk
    data.modelDisk_source (fun j => (data.modelDisk_smooth j).continuousOn)
    data.toTerminalSaddleGeometry.modelBand data.toTerminalSaddleGeometry.modelCaps
    ?_ ?_ ?_ data.model_disjoint i
  · intro j
    rw [image_comp, data.modelDisk_image]
    rfl
  · have hrange : range s = data.toTerminalSaddleGeometry.flatten ''
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) := by
      rw [image_image]
      ext y
      constructor
      · rintro ⟨q, rfl⟩
        exact mem_image_of_mem _ q.property
      · rintro ⟨q, hq, rfl⟩
        exact ⟨⟨q, hq⟩, rfl⟩
    rw [hrange, data.model_decomposition]
  · intro j
    change (fun x => data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk j x))) ''
        sphere (0 : E2) 1 ⊆ _
    rw [← data.model_boundary j]
    exact inter_subset_right

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies

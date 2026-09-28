import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProtectedGeometricInputs
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.LocalAtTarget












set_option autoImplicit false

open Set Metric Topology

namespace PoincareConjecture.M76

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {L : Submodule ℤ (κ → ℝ)} {α : Type*}

local notation "V" => ((ι → ℝ) × (κ → ℝ))
local notation "X" => LatticeHandleAmbient ι κ L
local notation "pi" => hamiltonMarkedProjection ι κ L
local notation "R0" => Set.prod (closedBall (0 : ι → ℝ) 1) (univ : Set (κ → ℝ))
local notation "R" => latticeHandleDomain ι κ L
local notation "W" => Set.prod (univ : Set (ι → ℝ)) (ball (0 : κ → ℝ) 2)

omit [Fintype ι] [Fintype κ] in
theorem continuous_hamiltonMarkedProjection : Continuous pi :=
  continuous_fst.prodMk (QuotientAddGroup.continuous_mk.comp continuous_snd)

omit [Fintype ι] [Fintype κ] in
theorem isOpenMap_hamiltonMarkedProjection : IsOpenMap pi :=
  IsOpenMap.id.prodMap QuotientAddGroup.isOpenMap_coe

omit [Fintype κ] in


theorem hamiltonMarkedProjection_mem_domain (x : V) : pi x ∈ R ↔ x ∈ R0 := Iff.rfl

namespace HamiltonRetainedBlockChart

variable {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
  {h : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) (Fin 3 → ℝ)}
  (retained : HamiltonRetainedBlockChart ι κ L e h)

include retained



theorem projection_injOn_open_window : InjOn pi W := by
  intro x hx y hy hxy
  have hz : (0 : ι → ℝ) ∈ closedBall (0 : ι → ℝ) 1 := mem_closedBall_self zero_le_one
  have hq : (QuotientAddGroup.mk x.2 : (κ → ℝ) ⧸ L.toAddSubgroup) =
      QuotientAddGroup.mk y.2 := congrArg (fun z : X ↦ z.2) hxy
  have heq : pi (0, x.2) = pi (0, y.2) := by
    change ((0 : ι → ℝ), QuotientAddGroup.mk x.2) = (0, QuotientAddGroup.mk y.2)
    exact Prod.ext rfl hq
  have hx0 : ((0 : ι → ℝ), x.2) ∈
      closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2 :=
    ⟨hz, ball_subset_closedBall hx.2⟩
  have hy0 : ((0 : ι → ℝ), y.2) ∈
      closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2 :=
    ⟨hz, ball_subset_closedBall hy.2⟩
  have htrans := retained.quotient_injective hx0 hy0 heq
  have hsnd := congrArg (fun z : V ↦ z.2) htrans
  exact Prod.ext (congrArg (fun z : X ↦ z.1) hxy) hsnd



noncomputable def projectionChart : OpenPartialHomeomorph V X :=
  OpenPartialHomeomorph.ofContinuousOpen
    (retained.projection_injOn_open_window.toPartialEquiv pi W)
    continuous_hamiltonMarkedProjection.continuousOn
    isOpenMap_hamiltonMarkedProjection (isOpen_univ.prod isOpen_ball)

@[simp] theorem projectionChart_apply (x : V) : retained.projectionChart x = pi x := rfl

@[simp] theorem projectionChart_source : retained.projectionChart.source = W := rfl

@[simp] theorem projectionChart_target : retained.projectionChart.target = pi '' W := rfl


theorem projection_isOpenEmbedding :
    IsOpenEmbedding (fun x : W ↦ pi (x : V)) :=
  retained.projectionChart.isOpenEmbedding_restrict

theorem projectionChart_isImage {P : Set V} (hPW : P ⊆ W) :
    retained.projectionChart.IsImage P (pi '' P) := by
  intro x hx
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact retained.projection_injOn_open_window (hPW hy) hx hyx ▸ hy
  · intro hp
    exact mem_image_of_mem pi hp



theorem projection_frontier [DiscreteTopology L] {P : Set V}
    (hP : IsCompact P) (hPW : P ⊆ W) :
    frontier (pi '' P) = pi '' frontier P := by
  have hFP : frontier P ⊆ retained.projectionChart.source :=
    hP.isClosed.frontier_subset.trans hPW
  have himage : IsCompact (pi '' P) := hP.image continuous_hamiltonMarkedProjection
  have hFT : frontier (pi '' P) ⊆ retained.projectionChart.target := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := himage.isClosed.frontier_subset hx
    exact ⟨y, hPW hy, rfl⟩
  have hf := (retained.projectionChart_isImage hPW).frontier.image_eq
  rw [inter_eq_right.mpr hFP, inter_eq_right.mpr hFT] at hf
  exact hf.symm


theorem projection_mem_interior_iff {P : Set V} (hPW : P ⊆ W)
    {x : V} (hx : x ∈ W) : pi x ∈ interior (pi '' P) ↔ x ∈ interior P :=
  (retained.projectionChart_isImage hPW).interior hx

end HamiltonRetainedBlockChart


def relativeMarkedProjection (x : R0) : R := ⟨pi x, x.property⟩

omit [Fintype κ] in
theorem continuous_relativeMarkedProjection :
    Continuous (relativeMarkedProjection (ι := ι) (κ := κ) (L := L)) :=
  (continuous_hamiltonMarkedProjection.comp continuous_subtype_val).subtype_mk _

omit [Fintype κ] in
theorem isOpenMap_relativeMarkedProjection :
    IsOpenMap (relativeMarkedProjection (ι := ι) (κ := κ) (L := L)) :=
  isOpenMap_hamiltonMarkedProjection.restrictPreimage R

namespace HamiltonRetainedBlockChart

variable {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
  {h : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) (Fin 3 → ℝ)}
  (retained : HamiltonRetainedBlockChart ι κ L e h)

include retained

local notation "Wr" => ((Subtype.val : R0 → V) ⁻¹' W)
local notation "pir" => (relativeMarkedProjection (ι := ι) (κ := κ) (L := L))

theorem relativeProjection_injOn_open_window : InjOn pir Wr := by
  intro x hx y hy hxy
  exact Subtype.ext (retained.projection_injOn_open_window hx hy (congrArg Subtype.val hxy))



noncomputable def relativeProjectionChart : OpenPartialHomeomorph R0 R := by
  have : Nonempty R0 := ⟨⟨0, mem_closedBall_self zero_le_one, mem_univ _⟩⟩
  exact OpenPartialHomeomorph.ofContinuousOpen
    (retained.relativeProjection_injOn_open_window.toPartialEquiv pir Wr)
    continuous_relativeMarkedProjection.continuousOn isOpenMap_relativeMarkedProjection
    ((isOpen_univ.prod isOpen_ball).preimage continuous_subtype_val)

@[simp] theorem relativeProjectionChart_apply (x : R0) :
    retained.relativeProjectionChart x = pir x := rfl

@[simp] theorem relativeProjectionChart_source :
    retained.relativeProjectionChart.source = Wr := rfl

theorem relativeProjectionChart_isImage {P : Set V} (hPW : P ⊆ W) :
    retained.relativeProjectionChart.IsImage
      ((Subtype.val : R0 → V) ⁻¹' P) ((Subtype.val : R → X) ⁻¹' (pi '' P)) := by
  intro x hx
  change pi (x : V) ∈ pi '' P ↔ (x : V) ∈ P
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact retained.projection_injOn_open_window (hPW hy) hx hyx ▸ hy
  · intro hp
    exact mem_image_of_mem pi hp



theorem projection_mem_relative_interior_iff {P : Set V} (hPW : P ⊆ W)
    (x : R0) (hx : (x : V) ∈ W) :
    pir x ∈ interior ((Subtype.val : R → X) ⁻¹' (pi '' P)) ↔
      x ∈ interior ((Subtype.val : R0 → V) ⁻¹' P) :=
  (retained.relativeProjectionChart_isImage hPW).interior hx

end HamiltonRetainedBlockChart

omit [Fintype κ] in


theorem hamiltonMarkedProjection_mem_frontier [Nonempty ι] (x : V) :
    pi x ∈ frontier R ↔ x ∈ frontier R0 := by
  change pi x ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ
    (univ : Set ((κ → ℝ) ⧸ L.toAddSubgroup))) ↔
    x ∈ frontier (closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)))
  simp only [frontier_prod_univ_eq]
  rfl

omit [Fintype κ] in


theorem hamiltonMarkedProjection_image_inter_frontier [Nonempty ι] (P : Set V) :
    (pi '' P) ∩ frontier R = pi '' (P ∩ frontier R0) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hfront⟩
    exact ⟨y, ⟨hy, (hamiltonMarkedProjection_mem_frontier y).mp hfront⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hfront⟩, rfl⟩
    exact ⟨mem_image_of_mem pi hy, (hamiltonMarkedProjection_mem_frontier y).mpr hfront⟩

end PoincareConjecture.M76

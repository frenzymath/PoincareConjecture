import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Disks.Coordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Domains.ChartImage












set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.ProtectedDisks

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

variable (L : Submodule ℤ V1)
local notation "X" => LatticeHandleAmbient (Fin 2) (Fin 1) L
local notation "pi" => hamiltonMarkedProjection (Fin 2) (Fin 1) L
local notation "R" => latticeHandleDomain (Fin 2) (Fin 1) L


def ambientSlab (b : Bool) : Set X :=
  univ ×ˢ ((QuotientAddGroup.mk : V1 → V1 ⧸ L.toAddSubgroup) '' transverse b)

theorem ambientSlab_isOpen (b : Bool) : IsOpen (ambientSlab L b) :=
  isOpen_univ.prod (QuotientAddGroup.isOpenMap_coe _ (transverse_isOpen b))

theorem sourceSlab_subset_block (b : Bool) :
    sourceSlab b ⊆ D2 ×ˢ closedBall (0 : V1) 2 := by
  intro x hx
  exact ⟨hx.1, mem_closedBall_zero_iff.mpr (transverse_norm hx.2).2.le⟩

theorem sourceSlab_projection_mem {b : Bool} {x : V2 × V1} (hx : x ∈ sourceSlab b) :
    pi x ∈ ambientSlab L b := ⟨mem_univ _, x.2, hx.2, rfl⟩

variable {α : Type*}
  {e : α → OpenPartialHomeomorph (LatticeHandleAmbient (Fin 2) (Fin 1) L) V3}
  {h : OpenPartialHomeomorph (V2 × V1) V3}
  (retained : HamiltonRetainedBlockChart (Fin 2) (Fin 1) L e h)

include retained

theorem ambientSlab_disjoint : Disjoint (ambientSlab L false) (ambientSlab L true) := by
  apply disjoint_left.mpr
  rintro z ⟨_, y, hy, hyz⟩ ⟨_, w, hw, hwz⟩
  have h0 : (0 : V2) ∈ D2 := by simp
  have heq : pi (0, y) = pi (0, w) := Prod.ext rfl (hyz.trans hwz.symm)
  have hi := retained.quotient_injective
    (sourceSlab_subset_block false ⟨h0, hy⟩) (sourceSlab_subset_block true ⟨h0, hw⟩) heq
  have hyw : y = w := congrArg Prod.snd hi
  subst w
  exact disjoint_left.mp transverse_disjoint hy hw


def chartSlab (b : Bool) : TopologicalSpace.Opens V3 :=
  ⟨(e retained.index).target ∩ (e retained.index).symm ⁻¹' ambientSlab L b,
    (e retained.index).symm.continuousOn.isOpen_inter_preimage
      (e retained.index).open_target (ambientSlab_isOpen L b)⟩

theorem chartSlab_subset_target (b : Bool) :
    (chartSlab L retained b : Set V3) ⊆ (e retained.index).target := inter_subset_left

theorem chartSlab_disjoint :
    Disjoint (chartSlab L retained false : Set V3) (chartSlab L retained true : Set V3) := by
  apply disjoint_left.mpr
  intro z hm hp
  exact disjoint_left.mp (ambientSlab_disjoint L retained) hm.2 hp.2

theorem chartSlab_inverse_formula {b : Bool} {x : V2 × V1} (hx : x ∈ sourceSlab b) :
    (e retained.index).symm (h x) = pi x := by
  rw [← retained.formula x (sourceSlab_subset_block b hx)]
  exact (e retained.index).left_inv (retained.contains x (sourceSlab_subset_block b hx))

theorem slab_subset_chartSlab (b : Bool) : slab h b ⊆ (chartSlab L retained b : Set V3) := by
  rintro z ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← retained.formula x (sourceSlab_subset_block b hx)]
    exact (e retained.index).mapsTo (retained.contains x (sourceSlab_subset_block b hx))
  · change (e retained.index).symm (h x) ∈ ambientSlab L b
    rw [chartSlab_inverse_formula L retained hx]
    exact sourceSlab_projection_mem L hx

theorem chartSlab_nonempty (b : Bool) : Nonempty (chartSlab L retained b) := by
  have hx : ((0 : V2), height b) ∈ sourceSlab b :=
    ⟨by simp, height_mem_transverse b⟩
  exact ⟨⟨h (0, height b), slab_subset_chartSlab L retained b ⟨_, hx, rfl⟩⟩⟩



theorem chartSlab_domain_image (b : Bool) :
    (Subtype.val : chartSlab L retained b → V3) ''
        {z : chartSlab L retained b | (e retained.index).symm (z : V3) ∈ R} = slab h b := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨v, hv, hve⟩ := y.property.2.2
    let x : V2 × V1 := (((e retained.index).symm y).1, v)
    have hx : x ∈ sourceSlab b := ⟨hy.1, hv⟩
    have hproj : pi x = (e retained.index).symm y := Prod.ext rfl hve
    refine ⟨x, hx, ?_⟩
    rw [← retained.formula x (sourceSlab_subset_block b hx), hproj]
    exact (e retained.index).right_inv y.property.1
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨h x, slab_subset_chartSlab L retained b ⟨x, hx, rfl⟩⟩, ?_, rfl⟩
    change (e retained.index).symm (h x) ∈ R
    rw [chartSlab_inverse_formula L retained hx]
    exact ⟨hx.1, mem_univ _⟩



theorem projected_slab_protected {b : Bool} {x : V2 × V1} (hx : x ∈ sourceSlab b) :
    pi x ∈ hamiltonHandleBlock (Fin 2) (Fin 1) L 2 \
      hamiltonHandleBlock (Fin 2) (Fin 1) L 1 := by
  refine ⟨⟨x, sourceSlab_subset_block b hx, rfl⟩, ?_⟩
  rintro ⟨y, hy, heq⟩
  have hy2 : y ∈ D2 ×ˢ closedBall (0 : V1) 2 :=
    ⟨hy.1, closedBall_subset_closedBall (by norm_num : (1 : ℝ) ≤ 2) hy.2⟩
  have hi : y = x := retained.quotient_injective hy2 (sourceSlab_subset_block b hx) heq
  have hx1 : ‖x.2‖ ≤ 1 := mem_closedBall_zero_iff.mp (hi ▸ hy.2)
  exact (not_le_of_gt (transverse_norm hx.2).1) hx1

omit retained in
theorem projected_slab_outer_open {b : Bool} {x : V2 × V1} (hx : x ∈ sourceSlab b) :
    pi x ∈ pi '' (D2 ×ˢ ball (0 : V1) 2) :=
  ⟨x, ⟨hx.1, mem_ball_zero_iff.mpr (transverse_norm hx.2).2⟩, rfl⟩



theorem diskMap_inverse_old_boundary_iff (b : Bool) (x : D2) :
    (e retained.index).symm (diskMap h b x) ∈ frontier R ↔ (x : V2) ∈ Q2 := by
  rw [show diskMap h b x = h ((x : V2), height b) from rfl,
    chartSlab_inverse_formula L retained ⟨x.property, height_mem_transverse b⟩]
  rw [latticeHandleDomain, frontier_prod_univ_eq, frontier_closedBall _ one_ne_zero]
  exact and_iff_left (mem_univ _)


def chartDomain (b : Bool) : Set (chartSlab L retained b) :=
  {z | (e retained.index).symm (z : V3) ∈ R}

theorem chartDomain_PL (he : PLDomain e R) (b : Bool) :
    PLDomain (fun _ : Unit => (chartSlab L retained b).openPartialHomeomorphSubtypeCoe
      (chartSlab_nonempty L retained b)) (chartDomain L retained b) :=
  he.chart_image retained.index (chartSlab L retained b)
    (chartSlab_nonempty L retained b) (chartSlab_subset_target L retained b)

theorem diskMap_inverse_mem (b : Bool) (x : D2) :
    (e retained.index).symm (diskMap h b x) ∈ R := by
  change (e retained.index).symm (h ((x : V2), height b)) ∈ R
  rw [chartSlab_inverse_formula L retained ⟨x.property, height_mem_transverse b⟩]
  exact ⟨x.property, mem_univ _⟩



noncomputable def chartFilling
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source) (b : Bool) :
    C(D2, chartDomain L retained b) where
  toFun x := ⟨⟨diskMap h b x, slab_subset_chartSlab L retained b
    ⟨((x : V2), height b), ⟨x.property, height_mem_transverse b⟩, rfl⟩⟩,
      diskMap_inverse_mem L retained b x⟩
  continuous_toFun := ((h.continuousOn.comp_continuous
    (continuous_subtype_val.prodMk continuous_const)
    (fun x => hsource ⟨x.property, mem_univ _⟩)).subtype_mk _).subtype_mk _

theorem chartFilling_apply
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source) (b : Bool) (x : D2) :
    ((chartFilling L retained hsource b x : chartSlab L retained b) : V3) =
      diskMap h b x := rfl

theorem chartFilling_rim
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source) (b : Bool) (x : Q2) :
    ((chartFilling L retained hsource b ⟨x, sphere_subset_closedBall x.property⟩ :
      chartSlab L retained b) : V3) = (rim h hsource b x : V3) := rfl

theorem rim_inverse_frontier
    (hsource : D2 ×ˢ (univ : Set V1) ⊆ h.source) (b : Bool) (x : Q2) :
    (e retained.index).symm (rim h hsource b x) ∈ frontier R :=
  (diskMap_inverse_old_boundary_iff L retained b
    ⟨x, sphere_subset_closedBall x.property⟩).mpr x.property

theorem inverse_chartDomain_protected (b : Bool) (z : chartDomain L retained b) :
    (e retained.index).symm ((z : chartSlab L retained b) : V3) ∈
        hamiltonHandleBlock (Fin 2) (Fin 1) L 2 \
          hamiltonHandleBlock (Fin 2) (Fin 1) L 1 ∧
      (e retained.index).symm ((z : chartSlab L retained b) : V3) ∈
        pi '' (D2 ×ˢ ball (0 : V1) 2) := by
  have hz : ((z : chartSlab L retained b) : V3) ∈ slab h b :=
    (chartSlab_domain_image L retained b).subset ⟨z, z.property, rfl⟩
  obtain ⟨x, hx, heq⟩ := hz
  rw [← heq, chartSlab_inverse_formula L retained hx]
  exact ⟨projected_slab_protected L retained hx, projected_slab_outer_open L hx⟩

end PoincareConjecture.M76.Dehn.ProtectedDisks

import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.SourceSlabHeight
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CirclePhaseIntervals

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

theorem sourceSurface_isCompact (phi : C(H, H)) (c : C) :
    IsCompact (sourceSurface phi c) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : CompactSpace R := isCompact_iff_compactSpace.mp
    (isCompact_latticeHandleDomain (Fin 1) (Fin 2) L)
  exact ((isClosed_singleton.preimage ((sourcePhase phi).continuous.comp
    (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous)).isCompact).image continuous_subtype_val

theorem sourceSurface_nonempty (phi : C(H, H)) (c : C)
    (F : (ContinuousMap.id H).HomotopyRel phi (latticeHandleBoundary (Fin 1) (Fin 2) L)) :
    (sourceSurface phi c).Nonempty := by
  let b : Metric.closedBall (0 : Fin 1 → ℝ) 1 := ⟨fun _ => 1, by simp⟩
  obtain ⟨x, _, _, hx⟩ := sourcePhase_boundary_surjective phi F b (by simp [b]) c
  let E := latticeHandleDomainEquiv (Fin 1) (Fin 2) L
  refine ⟨E.symm x, (mem_sourceSurface_iff phi c (E.symm x)).mpr ?_⟩
  rwa [E.apply_symm_apply]

theorem sourceSurface_subset_slab (phi : C(H, H)) {lo hi c : ℝ} (hc : c ∈ Icc lo hi) :
    sourceSurface phi (c : C) ⊆ sourceSlab phi lo hi := by
  intro x hx
  let xR : R := ⟨x, sourceSurface_subset phi (c : C) hx⟩
  apply (mem_sourceSlab_iff phi lo hi xR).mpr
  rw [(mem_sourceSurface_iff phi (c : C) xR).mp hx]
  exact ⟨c, hc, rfl⟩

noncomputable def sourceSurfaceHeightCoordinates (phi : C(H, H)) (lo hi c : ℝ)
    (hlo : 0 ≤ lo) (hhi : hi < p) (hc : c ∈ Icc lo hi) :
    sourceSurface phi (c : C) ≃ₜ
      {x : sourceSlab phi lo hi | sourceSlabHeight phi lo hi hlo hhi x = c} where
  toFun x := ⟨⟨x, sourceSurface_subset_slab phi hc x.property⟩,
    (sourceSlabHeight_eq_iff phi lo hi hlo hhi _ hc).mpr x.property⟩
  invFun x := ⟨x.val, (sourceSlabHeight_eq_iff phi lo hi hlo hhi x.val hc).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def sourcePhaseBand (phi : C(H, H)) (a b : ℝ) : Set R :=
  {x | sourcePhase phi (latticeHandleDomainEquiv (Fin 1) (Fin 2) L x) ∈
    AddCircle.openIntervalArc p a b}

theorem isOpen_sourcePhaseBand (phi : C(H, H)) (a b : ℝ) :
    IsOpen (sourcePhaseBand phi a b) :=
  (AddCircle.isOpen_openIntervalArc p a b).preimage
    ((sourcePhase phi).continuous.comp (latticeHandleDomainEquiv (Fin 1) (Fin 2) L).continuous)

noncomputable def sourceBandHeightCoordinates (phi : C(H, H)) (lo hi a b : ℝ)
    (hlo : 0 ≤ lo) (hhi : hi < p) (hla : lo < a) (hbh : b < hi) :
    {x : sourceSlab phi lo hi | sourceSlabHeight phi lo hi hlo hhi x ∈ Ioo a b} ≃ₜ
      sourcePhaseBand phi a b := by
  let height := sourceSlabHeight phi lo hi hlo hhi
  have hto (x : sourceSlab phi lo hi) (hx : height x ∈ Ioo a b) :
      (⟨x.val, sourceSlab_subset phi lo hi x.property⟩ : R) ∈ sourcePhaseBand phi a b := by
    exact ⟨height x, hx, sourceSlabHeight_coe phi lo hi hlo hhi x⟩
  have hfrom (x : sourcePhaseBand phi a b) :
      ∃ hx : (x.val : X) ∈ sourceSlab phi lo hi,
        height ⟨x.val, hx⟩ ∈ Ioo a b := by
    obtain ⟨t, ht, htx⟩ := x.property
    have htI : t ∈ Icc lo hi := ⟨(hla.trans ht.1).le, (ht.2.trans hbh).le⟩
    have hxS : (x.val : X) ∈ sourceSurface phi (t : C) :=
      (mem_sourceSurface_iff phi (t : C) x.val).mpr htx.symm
    have hxN := sourceSurface_subset_slab phi htI hxS
    refine ⟨hxN, ?_⟩
    have heq := (sourceSlabHeight_eq_iff phi lo hi hlo hhi ⟨x.val, hxN⟩ htI).mpr hxS
    change height ⟨x.val, hxN⟩ = t at heq
    rwa [heq]
  choose hxN hxheight using hfrom
  exact {
    toFun := fun x => ⟨⟨x.val, sourceSlab_subset phi lo hi x.val.property⟩, hto x.val x.property⟩
    invFun := fun x => ⟨⟨x.val, hxN x⟩, hxheight x⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
    continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _ }

end PoincareConjecture.M76.HamiltonIntervalTorus

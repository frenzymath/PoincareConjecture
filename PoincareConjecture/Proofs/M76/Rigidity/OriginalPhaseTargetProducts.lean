import PoincareConjecture.Proofs.M76.Rigidity.OriginalTargetTranslation
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

noncomputable def hamiltonZeroPhaseProduct (theta : ℝ) : C((C0 × C0) × ℝ, X0) :=
  ⟨fun z => (Q0).symm (z.1, ((theta + z.2 : ℝ) : C0)),
    (Q0).symm.continuous.comp (continuous_fst.prodMk
      ((AddCircle.continuous_mk' (4 * (16 : ℝ))).comp
        (continuous_const.add continuous_snd)))⟩

theorem hamiltonZeroPhaseProduct_coordinates (theta : ℝ) (z : (C0 × C0) × ℝ) :
    Q0 (hamiltonZeroPhaseProduct theta z) = (z.1, ((theta + z.2 : ℝ) : C0)) :=
  (Q0).apply_symm_apply _

theorem hamiltonZeroPhaseProduct_zero (theta : ℝ) (z : C0 × C0) :
    hamiltonZeroPhaseProduct theta (z, 0) = (Q0).symm (z, (theta : C0)) := by
  change (Q0).symm (z, ((theta + 0 : ℝ) : C0)) = _
  rw [add_zero]

theorem image_hamiltonZeroPhaseProduct (theta : ℝ) (T : Set ℝ) :
    hamiltonZeroPhaseProduct theta '' ((univ : Set (C0 × C0)) ×ˢ T) =
      (fun y : X0 => (Q0 y).2) ⁻¹' ((fun t : ℝ => ((theta + t : ℝ) : C0)) '' T) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change (Q0 (hamiltonZeroPhaseProduct theta z)).2 ∈
      ((fun t : ℝ => ((theta + t : ℝ) : C0)) '' T)
    rw [hamiltonZeroPhaseProduct_coordinates]
    exact ⟨z.2, hz.2, rfl⟩
  · rintro ⟨t, ht, he⟩
    refine ⟨((Q0 y).1, t), ⟨mem_univ _, ht⟩, ?_⟩
    apply (Q0).injective
    rw [hamiltonZeroPhaseProduct_coordinates]
    exact Prod.ext rfl he

theorem image_hamiltonZeroPhaseProduct_Icc (theta rho : ℝ) :
    hamiltonZeroPhaseProduct theta '' ((univ : Set (C0 × C0)) ×ˢ Icc (-rho) rho) =
      (fun y : X0 => (Q0 y).2) ⁻¹'
        AddCircle.closedIntervalArc (4 * 16) (theta - rho) (theta + rho) := by
  rw [image_hamiltonZeroPhaseProduct]
  apply congrArg (fun A : Set C0 => (fun y : X0 => (Q0 y).2) ⁻¹' A)
  ext v
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨theta + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t - theta, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    exact congrArg (fun u : ℝ => (u : C0)) (show theta + (t - theta) = t by ring)

theorem isEmbedding_hamiltonZeroPhaseProduct {theta rho : ℝ}
    (hlower : 0 < theta - rho) (hupper : theta + rho < 4 * 16) :
    Topology.IsEmbedding
      (fun z : ((univ : Set (C0 × C0)) ×ˢ Icc (-rho) rho : Set ((C0 × C0) × ℝ)) =>
        hamiltonZeroPhaseProduct theta z) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).symm.t2Space
  let P : Set ((C0 × C0) × ℝ) := univ ×ˢ Icc (-rho) rho
  let : CompactSpace P := isCompact_iff_compactSpace.mp
    (isCompact_univ.prod isCompact_Icc)
  have hc : Continuous (fun z : P => hamiltonZeroPhaseProduct theta z) :=
    (hamiltonZeroPhaseProduct theta).continuous.comp continuous_subtype_val
  have hi : Function.Injective (fun z : P => hamiltonZeroPhaseProduct theta z) := by
    intro z w he
    have hpair := congrArg Q0 he
    simp only [hamiltonZeroPhaseProduct_coordinates] at hpair
    have hz : theta + z.val.2 ∈ Ico (0 : ℝ) (0 + 4 * 16) :=
      ⟨by linarith [z.property.2.1], by linarith [z.property.2.2]⟩
    have hw : theta + w.val.2 ∈ Ico (0 : ℝ) (0 + 4 * 16) :=
      ⟨by linarith [w.property.2.1], by linarith [w.property.2.2]⟩
    have ht : theta + z.val.2 = theta + w.val.2 :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico hz hw).mp (congrArg Prod.snd hpair)
    have hfirst := congrArg Prod.fst hpair
    apply Subtype.ext
    exact Prod.ext hfirst (by linarith)
  exact (hc.isClosedEmbedding hi).isEmbedding

theorem isOpen_image_hamiltonZeroPhaseProduct {theta eps : ℝ}
    (hlower : 0 < theta - eps) (hupper : theta + eps < 4 * 16) :
    IsOpen (hamiltonZeroPhaseProduct theta ''
      ((univ : Set (C0 × C0)) ×ˢ Ioo (-eps) eps)) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  have heq : (fun t : ℝ => ((theta + t : ℝ) : C0)) '' Ioo (-eps) eps =
      interior (AddCircle.closedIntervalArc (4 * 16) (theta - eps) (theta + eps)) := by
    rw [AddCircle.interior_closedIntervalArc (4 * 16) hlower hupper]
    ext v
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨theta + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t - theta, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      exact congrArg (fun u : ℝ => (u : C0)) (show theta + (t - theta) = t by ring)
  rw [image_hamiltonZeroPhaseProduct, heq]
  exact isOpen_interior.preimage (continuous_snd.comp (Q0).continuous)

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.RimLabels
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.ComplementarySlabContraction

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_normalized_annulus_map
    (phi : C(H0, H0)) {R S : Set X0} {cut alpha beta : ℝ}
    (ha : cut < alpha) (hab : alpha < beta) (hb : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hfront : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (hSR : S ⊆ R) (H : Ann ≃ₜ S)
    (hrim : ∀ z : Ann,
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
        (H z : X0) ∈ frontier R) :
    ∃ (f : C(Ann, unitInterval × C0)) (label : Bool → Bool),
      (∀ z : Ann, (f z).2 = (Q0 (hamiltonZeroAmbientMap phi (H z))).1.1) ∧
      (∀ z : Ann, (((beta - alpha) * ((f z).1 : ℝ) + alpha : ℝ) : C0) =
        hamiltonZeroCircleMap phi (H z)) ∧
      ∀ side : Bool, ∀ z : Circle,
        f (Dehn.annulusRimPoint side z) =
          (if label side then 1 else 0,
            (Q0 (hamiltonZeroAmbientMap phi (H (Dehn.annulusRimPoint side z)))).1.1) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let J := AddCircle.openPartialHomeomorphCoe p cut
  let normal : C(Ann, C0) := ⟨fun z => hamiltonZeroCircleMap phi (H z),
    (hamiltonZeroCircleMap phi).continuous.comp (continuous_subtype_val.comp H.continuous)⟩
  have hn (z : Ann) : normal z ∈ AddCircle.closedIntervalArc p alpha beta := hR (hSR (H z).property)
  have hsource (u : ℝ) (hu : u ∈ Icc alpha beta) : u ∈ J.source :=
    ⟨ha.trans_le hu.1, hu.2.trans_lt hb⟩
  have htarget (z : Ann) : normal z ∈ J.target := by
    obtain ⟨u, hu, huf⟩ := hn z
    rw [← huf]
    exact J.map_source (hsource u hu)
  let lift : C(Ann, ℝ) := ⟨fun z => J.symm (normal z),
    J.continuousOn_symm.comp_continuous normal.continuous htarget⟩
  have hlift (z : Ann) : lift z ∈ Icc alpha beta ∧ (lift z : C0) = normal z := by
    obtain ⟨u, hu, huf⟩ := hn z
    have heq : lift z = u := by
      change J.symm (normal z) = u
      rw [← huf]
      exact J.left_inv (hsource u hu)
    rw [heq]
    exact ⟨hu, huf⟩
  let interval : C(Ann, Icc alpha beta) := ⟨fun z => ⟨lift z, (hlift z).1⟩,
    lift.continuous.subtype_mk _⟩
  let f : C(Ann, unitInterval × C0) :=
    ⟨fun z => (iccHomeoI alpha beta hab (interval z),
      (Q0 (hamiltonZeroAmbientMap phi (H z))).1.1), by fun_prop⟩
  obtain ⟨label, hlabel⟩ := exists_hamiltonZero_annulus_rim_labels phi hfront H hrim
  refine ⟨f, label, fun _ => rfl, ?_, ?_⟩
  · intro z
    have hinv := iccHomeoI_symm_apply_coe alpha beta hab ((f z).1)
    have heq : (beta - alpha) * ((f z).1 : ℝ) + alpha = lift z := by
      rw [← hinv]
      change ((iccHomeoI alpha beta hab).symm
        ((iccHomeoI alpha beta hab) (interval z)) : ℝ) = lift z
      rw [Homeomorph.symm_apply_apply]
      rfl
    rw [heq]
    exact (hlift z).2
  · intro side z
    apply Prod.ext
    · apply Subtype.ext
      have hvalue : lift (Dehn.annulusRimPoint side z) = if label side then beta else alpha := by
        change J.symm (normal (Dehn.annulusRimPoint side z)) = _
        rw [show normal (Dehn.annulusRimPoint side z) =
          if label side then (beta : C0) else (alpha : C0) from hlabel side z]
        cases h : label side
        · exact J.left_inv (hsource alpha ⟨le_rfl, hab.le⟩)
        · exact J.left_inv (hsource beta ⟨hab.le, le_rfl⟩)
      change ((iccHomeoI alpha beta hab) (interval (Dehn.annulusRimPoint side z)) : ℝ) = _
      rw [iccHomeoI_apply_coe]
      change (lift (Dehn.annulusRimPoint side z) - alpha) / (beta - alpha) = _
      rw [hvalue]
      cases label side <;> simp [ne_of_gt (sub_pos.mpr hab)]
    · rfl

end PoincareConjecture.M76

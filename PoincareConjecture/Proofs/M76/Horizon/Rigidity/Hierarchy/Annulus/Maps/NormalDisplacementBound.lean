import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.NormalizedMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Instances.AddCircle.Real










set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem hamiltonZero_annulus_normal_displacement_bound
    (u v : C(Ann, X0)) {cut alpha beta : ℝ}
    (halpha : cut < alpha) (_hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (hu : ∀ z : Ann, (Q0 (u z)).2 ∈ AddCircle.closedIntervalArc p alpha beta)
    (hv : ∀ z : Ann, (Q0 (v z)).2 ∈ AddCircle.closedIntervalArc p alpha beta)
    (w : C(Ann, ℝ))
    (hw : ∀ z : Ann, (w z : C0) = (Q0 (v z)).2 - (Q0 (u z)).2)
    (hzero : ∀ z : Ann, z ∈ Dehn.annulusRims → w z = 0) :
    let J := AddCircle.openPartialHomeomorphCoe p cut
    ∀ z : Ann,
      w z = J.symm ((Q0 (v z)).2) - J.symm ((Q0 (u z)).2) ∧
        J.symm ((Q0 (u z)).2) + w z ∈ Icc alpha beta := by
  intro J
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : PreconnectedSpace Ann := Dehn.annulusCylinderHomeomorph.surjective.denseRange.preconnectedSpace
    Dehn.annulusCylinderHomeomorph.continuous
  have hsource (t : ℝ) (ht : t ∈ Icc alpha beta) : t ∈ J.source :=
    ⟨halpha.trans_le ht.1, ht.2.trans_lt hbeta⟩
  have htarget (x : C0) (hx : x ∈ AddCircle.closedIntervalArc p alpha beta) : x ∈ J.target := by
    obtain ⟨t, ht, rfl⟩ := hx
    exact J.map_source (hsource t ht)
  have hlift (x : C0) (hx : x ∈ AddCircle.closedIntervalArc p alpha beta) :
      J.symm x ∈ Icc alpha beta ∧ ((J.symm x : ℝ) : C0) = x := by
    obtain ⟨t, ht, rfl⟩ := hx
    have htJ := J.left_inv (hsource t ht)
    change J.symm (t : C0) = t at htJ
    rw [htJ]
    exact ⟨ht, rfl⟩
  let U : C(Ann, ℝ) := ⟨fun z => J.symm ((Q0 (u z)).2),
    J.continuousOn_symm.comp_continuous ((Q0).continuous.comp u.continuous).snd
      (fun z => htarget _ (hu z))⟩
  let V : C(Ann, ℝ) := ⟨fun z => J.symm ((Q0 (v z)).2),
    J.continuousOn_symm.comp_continuous ((Q0).continuous.comp v.continuous).snd
      (fun z => htarget _ (hv z))⟩
  let D : C(Ann, ℝ) := w - (V - U)
  have hD (z : Ann) : (D z : C0) = 0 := by
    change ((w z - (V z - U z) : ℝ) : C0) = 0
    rw [AddCircle.coe_sub, AddCircle.coe_sub, hw z]
    change (Q0 (v z)).2 - (Q0 (u z)).2 -
      (((J.symm ((Q0 (v z)).2) : ℝ) : C0) - ((J.symm ((Q0 (u z)).2) : ℝ) : C0)) = 0
    rw [(hlift _ (hv z)).2, (hlift _ (hu z)).2, sub_self]
  let z0 : Ann := Dehn.annulusRimPoint false 0
  have hz0 : z0 ∈ Dehn.annulusRims := Or.inl ⟨0, rfl⟩
  have hnormal0 : (Q0 (v z0)).2 = (Q0 (u z0)).2 := by
    have h := hw z0
    rw [hzero z0 hz0, AddCircle.coe_zero] at h
    exact sub_eq_zero.mp h.symm
  have hD0 : D z0 = 0 := by
    change w z0 - (J.symm ((Q0 (v z0)).2) - J.symm ((Q0 (u z0)).2)) = 0
    rw [hzero z0 hz0, hnormal0, sub_self, sub_self]
  intro z
  have hz : D z = 0 :=
    ((AddCircle.isCoveringMap_coe p).const_of_comp D.continuous
      (fun x y => (hD x).trans (hD y).symm) z z0).trans hD0
  have heq : w z = V z - U z := sub_eq_zero.mp hz
  refine ⟨heq, ?_⟩
  change U z + w z ∈ Icc alpha beta
  rw [heq, add_sub_cancel]
  exact (hlift _ (hv z)).1

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Translations.DisplacementLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.HomotopyDisplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SourceDiskNormalForm
import Mathlib.Topology.Covering.AddCircle










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "V2" => (Fin 2 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => (Set.ofPred (fun z : Disk => (z : V2) ∈ sphere (0 : V2) 1))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_relative_disk_displacement
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j q : V2 → X0} (hj : PolyhedralPLInCharts e j Disk)
    (hq : PolyhedralPLInCharts d q Disk)
    {v : C(Disk, X0)} (hv : ∀ z : Disk, q z = v z)
    (hphase : ∀ z : Disk, (Q0 (v z)).1.1 =
      (Q0 (hamiltonZeroAmbientMap phi (j z))).1.1)
    (H : (⟨fun z : Disk => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩ :
      C(Disk, X0)).HomotopyRel v Rim) :
    ∃ w : V2 → V3, FinitePiecewiseAffineOn w Disk ∧
      (∀ z : Disk, w z 0 = 0) ∧
      (∀ z : Disk, z ∈ Rim → w z = 0) ∧
      ∀ z : Disk, hamiltonZeroTargetVectorTranslation
        (w z, hamiltonZeroAmbientMap phi (j z)) = q z := by
  classical
  let P : C(X0, C0 × C0) := ⟨fun x => ((Q0 x).1.2, (Q0 x).2), by fun_prop⟩
  obtain ⟨W, hW, hWzero⟩ := LinearTorus.exists_real_displacement_of_homotopyRel p
    (H.compContinuousMap P)
  let w : V2 → V3 := fun x =>
    if hx : x ∈ Disk then ![0, (W ⟨x, hx⟩).1, (W ⟨x, hx⟩).2] else 0
  have hwval (z : Disk) : w z = ![0, (W z).1, (W z).2] := by
    simp only [w, dif_pos z.property]
  have hwc : ContinuousOn w Disk := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h : Continuous (fun z : Disk => ![(0 : ℝ), (W z).1, (W z).2]) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_const
      · exact W.continuous.fst
      · exact W.continuous.snd
    exact h.congr (fun z => (hwval z).symm)
  have htranslation (z : Disk) : hamiltonZeroTargetVectorTranslation
      (w z, hamiltonZeroAmbientMap phi (j z)) = q z := by
    apply (Q0).injective
    rw [hamiltonZeroTargetVectorTranslation_coordinates, hv, hwval]
    have hsum :
        ((Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 + ((W z).1 : C0),
          (Q0 (hamiltonZeroAmbientMap phi (j z))).2 + ((W z).2 : C0)) =
        ((Q0 (v z)).1.2, (Q0 (v z)).2) := by
      have h := hW z
      change LinearTorus.quotientMap p (W z) =
        ((Q0 (v z)).1.2, (Q0 (v z)).2) -
          ((Q0 (hamiltonZeroAmbientMap phi (j z))).1.2,
            (Q0 (hamiltonZeroAmbientMap phi (j z))).2) at h
      change ((Q0 (hamiltonZeroAmbientMap phi (j z))).1.2,
        (Q0 (hamiltonZeroAmbientMap phi (j z))).2) +
        LinearTorus.quotientMap p (W z) = _
      rw [h]
      abel
    change (((Q0 (hamiltonZeroAmbientMap phi (j z))).1.1 + ((0 : ℝ) : C0),
      (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 + ((W z).1 : C0)),
      (Q0 (hamiltonZeroAmbientMap phi (j z))).2 + ((W z).2 : C0)) = _
    have hfirst := congrArg (fun x : C0 × C0 => x.1) hsum
    have hlast := congrArg (fun x : C0 × C0 => x.2) hsum
    have hmiddle : (Q0 (hamiltonZeroAmbientMap phi (j z))).1.1 + ((0 : ℝ) : C0) =
        (Q0 (v z)).1.1 := by simpa using (hphase z).symm
    exact Prod.ext (Prod.ext hmiddle hfirst) hlast
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  have hjK : PolyhedralPLInCharts e j K.space := by simpa only [hKs] using hj
  have hqK : PolyhedralPLInCharts d q K.space := by simpa only [hKs] using hq
  have hwPL := hd.finitePiecewiseAffineOn_displacement K hK
    (hphi.polyhedralPL_hamiltonZeroAmbientMap_comp K hK hjK) hqK w
    (by simpa only [hKs] using hwc)
    (fun x hx => htranslation ⟨x, hKs.subset hx⟩)
  refine ⟨w, by simpa only [hKs] using hwPL, ?_, ?_, htranslation⟩
  · intro z
    rw [hwval]
    rfl
  · intro z hz
    rw [hwval, hWzero z hz]
    ext i
    fin_cases i <;> rfl

theorem hamiltonZero_disk_coordinate_displacement_bound
    (u v : C(Disk, C0)) {cut alpha beta : ℝ}
    (halpha : cut < alpha) (_hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (hu : ∀ z : Disk, u z ∈ AddCircle.closedIntervalArc p alpha beta)
    (hv : ∀ z : Disk, v z ∈ AddCircle.closedIntervalArc p alpha beta)
    (w : C(Disk, ℝ))
    (hw : ∀ z : Disk, (w z : C0) = v z - u z)
    (hzero : ∀ z : Disk, z ∈ Rim → w z = 0) :
    let J := AddCircle.openPartialHomeomorphCoe p cut
    ∀ z : Disk,
      w z = J.symm (v z) - J.symm (u z) ∧
        J.symm (u z) + w z ∈ Icc alpha beta := by
  intro J
  let : PreconnectedSpace Disk := isPreconnected_iff_preconnectedSpace.mp
    (convex_closedBall (0 : V2) 1).isPreconnected
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
  let U : C(Disk, ℝ) := ⟨fun z => J.symm (u z),
    J.continuousOn_symm.comp_continuous u.continuous
      (fun z => htarget _ (hu z))⟩
  let V : C(Disk, ℝ) := ⟨fun z => J.symm (v z),
    J.continuousOn_symm.comp_continuous v.continuous
      (fun z => htarget _ (hv z))⟩
  let D : C(Disk, ℝ) := w - (V - U)
  have hD (z : Disk) : (D z : C0) = 0 := by
    change ((w z - (V z - U z) : ℝ) : C0) = 0
    rw [AddCircle.coe_sub, AddCircle.coe_sub, hw z]
    change v z - u z -
      (((J.symm (v z) : ℝ) : C0) - ((J.symm (u z) : ℝ) : C0)) = 0
    rw [(hlift _ (hv z)).2, (hlift _ (hu z)).2, sub_self]
  let z0 : Disk := ⟨(1 : V2), by simp [mem_closedBall, dist_eq_norm]⟩
  have hz0 : z0 ∈ Rim := by change (1 : V2) ∈ sphere 0 1; simp
  have hnormal0 : v z0 = u z0 := by
    have h := hw z0
    rw [hzero z0 hz0, AddCircle.coe_zero] at h
    exact sub_eq_zero.mp h.symm
  have hD0 : D z0 = 0 := by
    change w z0 - (J.symm (v z0) - J.symm (u z0)) = 0
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

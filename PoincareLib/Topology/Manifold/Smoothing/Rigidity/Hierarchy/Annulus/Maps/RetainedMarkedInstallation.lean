import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.MarkedInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.NormalDisplacementBound
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.RetainedArcDisplacement

/-!
# Installing a marked annulus while retaining its target arc

The canonical real-coordinate bound shows that clipping does not alter the
prescribed annulus endpoint. Clip the original-atlas displacement extension
before translation, so the whole retained region stays in the target arc
throughout the ambient homotopy.
-/

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_retained_marked_annulus_installation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
    {j q : ℝ × ℝ → X0} (hj : PolyhedralPLInCharts e j Ann)
    (hji : Topology.IsEmbedding (fun z : Ann => j z))
    (hjR : ∀ z : Ann, j z ∈ R)
    (hrim : ∀ z : Ann,
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔ j z ∈ frontier R)
    (hq : PolyhedralPLInCharts d q Ann)
    {v : C(Ann, X0)} (hv : ∀ z : Ann, q z = v z)
    (hphase : ∀ z : Ann, (Q0 (v z)).1.2 =
      (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2)
    (H : (⟨fun z : Ann => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩ :
      C(Ann, X0)).HomotopyRel v Dehn.annulusRims)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hvArc : ∀ z : Ann, (Q0 (v z)).2 ∈ AddCircle.closedIntervalArc p alpha beta) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      (∀ z : Ann, hamiltonZeroAmbientMap psi (j z) = v z) ∧
      (R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.2 = hamiltonZeroSecondCircleMap phi x) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let : Fact (0 < p) := ⟨by norm_num⟩
  let u : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j z),
    (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩
  obtain ⟨w, hw, hwphase, hwrim, hwval⟩ :=
    exists_hamiltonZero_relative_annulus_displacement hd hphi hj hq hv hphase H
  have hwdepth (z : Ann)
      (hz : depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1) : w z = 0 := by
    apply hwrim z
    rcases hz with hz | hz
    · exact Or.inl ((Dehn.range_annulusRimPoint false).symm.subset hz)
    · exact Or.inr ((Dehn.range_annulusRimPoint true).symm.subset hz)
  obtain ⟨W, hW, hWbase, hWzero, hWphase, hWoutside⟩ :=
    exists_original_retained_annulus_displacement_extension e heR hj hji
      (fun x hx => hjR ⟨x, hx⟩) hrim
      w hw (fun z hz => hwphase ⟨z, hz⟩) hwdepth
  have hWprotected (x : X0) (hx : x ∉ interior R) : W x = 0 := by
    by_cases hxR : x ∈ R
    · exact hWzero x ⟨subset_closure hxR, hx⟩
    · exact hWoutside x hxR
  let wn : C(Ann, ℝ) := ⟨fun z => w z 2,
    (continuous_apply 2).comp hw.continuousOn.domRestrict⟩
  have hwn (z : Ann) : (wn z : C0) = (Q0 (v z)).2 - (Q0 (u z)).2 := by
    have h := congrArg (fun x : X0 => (Q0 x).2) ((hwval z).trans (hv z))
    rw [hamiltonZeroTargetVectorTranslation_coordinates] at h
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  have hnBound := hamiltonZero_annulus_normal_displacement_bound u v halpha hab hbeta
    (fun z => hR (hjR z)) hvArc wn hwn (fun z hz => congrFun (hwrim z hz) 2)
  obtain ⟨V, hVPL, _, hVphase, _, hVzero, _, hVsame, hVarc⟩ :=
    exists_hamiltonZero_retained_arc_displacement hd hphi heR halpha hab hbeta hR
      W hW hWphase hWprotected
  have hVbase (z : Ann) : V (j z) = w z := by
    rw [hVsame (j z) (hjR z) (by
      rw [hWbase z]
      exact (hnBound z).2), hWbase z]
  obtain ⟨psi, hpsi, Hpsi, Fpsi, hsame, hformula, _, _⟩ :=
    hphi.exists_hamiltonZero_second_phase_adjustment hd F V hVPL hVphase hVzero
  let G : (hamiltonZeroAmbientMap phi).HomotopyRel
      (hamiltonZeroAmbientMap psi) (interior R)ᶜ := {
    toFun := fun z => hamiltonZeroTargetVectorTranslation
      ((z.1 : ℝ) • V z.2, hamiltonZeroAmbientMap phi z.2)
    continuous_toFun := hamiltonZeroTargetVectorTranslation.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).smul
        (V.continuous.comp continuous_snd)).prodMk
        ((hamiltonZeroAmbientMap phi).continuous.comp continuous_snd))
    map_zero_left := by
      intro x
      change hamiltonZeroTargetVectorTranslation ((0 : ℝ) • V x, _) = _
      rw [zero_smul, hamiltonZeroTargetVectorTranslation_zero]
    map_one_left := by
      intro x
      change hamiltonZeroTargetVectorTranslation ((1 : ℝ) • V x, _) = _
      rw [one_smul]
      exact (hformula x).symm
    prop' := by
      intro t x hx
      change hamiltonZeroTargetVectorTranslation ((t : ℝ) • V x, _) = _
      rw [hVzero x hx, smul_zero, hamiltonZeroTargetVectorTranslation_zero] }
  have hGarc (t : unitInterval) (x : X0) (hx : x ∈ R) :
      (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta := hVarc x hx t
  refine ⟨psi, hpsi, Hpsi, Fpsi, hsame, ?_, ?_, G, ?_, hGarc⟩
  · intro z
    rw [hformula, hVbase]
    exact (hwval z).trans (hv z)
  · intro x hx
    have h := hGarc 1 x hx
    rw [G.apply_one] at h
    exact h
  · intro t x
    change (Q0 (hamiltonZeroTargetVectorTranslation
      ((t : ℝ) • V x, hamiltonZeroAmbientMap phi x))).1.2 = _
    rw [hamiltonZeroTargetVectorTranslation_coordinates]
    simp only [Pi.smul_apply, smul_eq_mul, hVphase, mul_zero, AddCircle.coe_zero, add_zero]
    exact (hamiltonZeroSecondCircleMap_ambient phi x).symm

end PoincareMT.M76

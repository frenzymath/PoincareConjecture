import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.Translations.DisplacementLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.HomotopyDisplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.FoldedContraction










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_relative_annulus_displacement
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j q : ℝ × ℝ → X0} (hj : PolyhedralPLInCharts e j Ann)
    (hq : PolyhedralPLInCharts d q Ann)
    {v : C(Ann, X0)} (hv : ∀ z : Ann, q z = v z)
    (hphase : ∀ z : Ann, (Q0 (v z)).1.2 =
      (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2)
    (H : (⟨fun z : Ann => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩ :
      C(Ann, X0)).HomotopyRel v Dehn.annulusRims) :
    ∃ w : ℝ × ℝ → V3, FinitePiecewiseAffineOn w Ann ∧
      (∀ z : Ann, w z 1 = 0) ∧
      (∀ z : Ann, z ∈ Dehn.annulusRims → w z = 0) ∧
      ∀ z : Ann, hamiltonZeroTargetVectorTranslation
        (w z, hamiltonZeroAmbientMap phi (j z)) = q z := by
  classical
  let P : C(X0, C0 × C0) := ⟨fun x => ((Q0 x).1.1, (Q0 x).2), by fun_prop⟩
  obtain ⟨W, hW, hWzero⟩ := LinearTorus.exists_real_displacement_of_homotopyRel p
    (H.compContinuousMap P)
  let w : ℝ × ℝ → V3 := fun x =>
    if hx : x ∈ Ann then ![(W ⟨x, hx⟩).1, 0, (W ⟨x, hx⟩).2] else 0
  have hwval (z : Ann) : w z = ![(W z).1, 0, (W z).2] := by
    simp only [w, dif_pos z.property]
  have hwc : ContinuousOn w Ann := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have h : Continuous (fun z : Ann => ![(W z).1, (0 : ℝ), (W z).2]) := by
      apply continuous_pi
      intro i
      fin_cases i
      · exact W.continuous.fst
      · exact continuous_const
      · exact W.continuous.snd
    exact h.congr (fun z => (hwval z).symm)
  have htranslation (z : Ann) : hamiltonZeroTargetVectorTranslation
      (w z, hamiltonZeroAmbientMap phi (j z)) = q z := by
    apply (Q0).injective
    rw [hamiltonZeroTargetVectorTranslation_coordinates, hv, hwval]
    have hsum :
        ((Q0 (hamiltonZeroAmbientMap phi (j z))).1.1 + ((W z).1 : C0),
          (Q0 (hamiltonZeroAmbientMap phi (j z))).2 + ((W z).2 : C0)) =
        ((Q0 (v z)).1.1, (Q0 (v z)).2) := by
      have h := hW z
      change LinearTorus.quotientMap p (W z) =
        ((Q0 (v z)).1.1, (Q0 (v z)).2) -
          ((Q0 (hamiltonZeroAmbientMap phi (j z))).1.1,
            (Q0 (hamiltonZeroAmbientMap phi (j z))).2) at h
      change ((Q0 (hamiltonZeroAmbientMap phi (j z))).1.1,
        (Q0 (hamiltonZeroAmbientMap phi (j z))).2) +
        LinearTorus.quotientMap p (W z) = _
      rw [h]
      abel
    change (((Q0 (hamiltonZeroAmbientMap phi (j z))).1.1 + ((W z).1 : C0),
      (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 + ((0 : ℝ) : C0)),
      (Q0 (hamiltonZeroAmbientMap phi (j z))).2 + ((W z).2 : C0)) = _
    have hfirst := congrArg (fun x : C0 × C0 => x.1) hsum
    have hlast := congrArg (fun x : C0 × C0 => x.2) hsum
    have hmiddle : (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 + ((0 : ℝ) : C0) =
        (Q0 (v z)).1.2 := by simpa using (hphase z).symm
    exact Prod.ext (Prod.ext hfirst hmiddle) hlast
  obtain ⟨K, hK, hKs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (by norm_num : (0 : ℝ) < 1) (by norm_num : 4 * (1 : ℝ) < 8)
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

end PoincareConjecture.M76

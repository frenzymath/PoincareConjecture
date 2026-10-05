import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.SourceRimExtension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.MarkedStraightening
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.MarkedCoveringPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.FoldedContraction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.CoordinateHomotopy

/-!
# Marked annulus covering or folded contraction

The actual normalized source map supplies the full rim labels.  Its circle
lift constructs the finite PL rim extension.  Distinct labels give a marked
covering with its original-target PL formula; equal labels give the relative
normal contraction.  Both conclusions retain the actual ambient homotopy.
-/

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C64" => AddCircle (4 * (16 : ℝ))
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_annulus_marked_or_folded
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    {j : ℝ × ℝ → X0} (hj : PolyhedralPLInCharts e j Ann)
    {theta : C64} {cut alpha beta : ℝ}
    (hcut : cut < alpha) (hab : alpha < beta)
    (hbeta : beta < cut + (4 * (16 : ℝ)))
    (hphase : ∀ z : Ann, (Q0 (hamiltonZeroAmbientMap phi (j z))).1.2 = theta)
    (f : C(Ann, unitInterval × C64)) (label : Bool → Bool)
    (hf : ∀ z : Ann, (f z).2 = (Q0 (hamiltonZeroAmbientMap phi (j z))).1.1)
    (hnormal : ∀ z : Ann, (((beta - alpha) * ((f z).1 : ℝ) + alpha : ℝ) : C64) =
      (Q0 (hamiltonZeroAmbientMap phi (j z))).2)
    (hlabels : ∀ side z, (f (Dehn.annulusRimPoint side z)).1 =
      if label side then 1 else 0)
    (g : C(Circle, C64))
    (hg : ∀ z, g z = (Q0 (hamiltonZeroAmbientMap phi
      (j (Dehn.annulusRimPoint false z)))).1.1)
    (hgc : IsCoveringMap g) (Hrim : Circle ≃ₜ Circle)
    (L : (ContinuousMap.id Circle).Homotopy (Hrim : C(Circle, Circle)))
    (hlift : ∀ t z, g (L (t, z)) =
      (f (Dehn.annulusCylinderHomeomorph (t, z))).2) :
    let u : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j z),
      (hamiltonZeroAmbientMap phi).continuous.comp hj.continuousOn.domRestrict⟩
    (label false = label true ∧
      PolyhedralPLInCharts d
        (hamiltonZeroTargetPhaseRetraction (if label false then beta else alpha) ∘
          hamiltonZeroAmbientMap phi ∘ j) Ann ∧
      Nonempty (u.HomotopyRel
        ((hamiltonZeroTargetPhaseRetraction (if label false then beta else alpha)).comp u)
        Dehn.annulusRims)) ∨
    (label false ≠ label true ∧
      ∃ c : C(Ann, unitInterval × C64), IsCoveringMap c ∧
        Nonempty (f.HomotopyRel c Dehn.annulusRims) ∧
        ∃ q : ℝ × ℝ → X0, PolyhedralPLInCharts d q Ann ∧
          (∀ x : Ann, q x = hamiltonZeroAnnulusTargetMap alpha beta theta (c x)) ∧
          Nonempty (u.HomotopyRel
            ((hamiltonZeroAnnulusTargetMap alpha beta theta).comp c) Dehn.annulusRims)) := by
  intro u
  have hrim (side : Bool) (z : Circle) :
      (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint side z)))).2 =
        ((if label side then beta else alpha : ℝ) : C64) := by
    rw [← hnormal, hlabels]
    cases label side <;> simp
  by_cases hsame : label false = label true
  · have hlabel (side : Bool) : label side = label false := by
      cases side
      · rfl
      · exact hsame.symm
    have hend : (if label false then beta else alpha) ∈ Icc alpha beta := by
      cases label false <;> exact ⟨by simp [hab.le], by simp [hab.le]⟩
    have hslab (z : Ann) : (Q0 (u z)).2 ∈
        AddCircle.closedIntervalArc (4 * (16 : ℝ)) alpha beta := by
      change (Q0 (hamiltonZeroAmbientMap phi (j z))).2 ∈ _
      rw [← hnormal]
      refine ⟨(beta - alpha) * ((f z).1 : ℝ) + alpha, ⟨?_, ?_⟩, rfl⟩
      · nlinarith [(f z).1.property.1]
      · nlinarith [(f z).1.property.2]
    obtain ⟨hPL, T, _, _, _⟩ := hphi.exists_hamiltonZero_folded_annulus_contraction
      hd hcut hbeta hend j hj hslab (fun side z => by rw [hrim, hlabel side])
    exact Or.inl ⟨hsame, hPL, ⟨T⟩⟩
  · have hcover : IsCoveringMap (fun z : Circle =>
        (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint false z)))).1.1) := by
      convert hgc using 1
      funext z
      exact (hg z).symm
    have hupper (z : Circle) :
        (Q0 (hamiltonZeroAmbientMap phi
          (j (Dehn.annulusRimPoint false (Hrim z))))).1.1 =
        (Q0 (hamiltonZeroAmbientMap phi (j (Dehn.annulusRimPoint true z)))).1.1 := by
      have h := hlift 1 z
      rw [L.apply_one, Dehn.annulusCylinderHomeomorph_one, hg, hf] at h
      exact h
    obtain ⟨A, hA, hA0, hA1⟩ := exists_hamiltonZero_source_annulus_rim_extension
      hd hphi hj hphase (hrim false) hcover Hrim L hupper
    obtain ⟨D, hD, c, hc, hcf, Hc⟩ :=
      Dehn.exists_relative_annulus_covering_of_opposite_rims f g hgc Hrim L hlift
        label hsame hlabels A hA hA0 hA1
    obtain ⟨q, hq, hqval⟩ := exists_hamiltonZero_oriented_marked_annulus_covering_PL
      hd hphi hj (label false) (fun z => hphase _) (hrim false) D hD
    have hqtarget (x : Ann) : q x = hamiltonZeroAnnulusTargetMap alpha beta theta (c x) := by
      rw [hqval, hcf]
      simp only [hamiltonZeroAnnulusTargetMap, ContinuousMap.coe_mk,
        Dehn.annulusTargetReflection, Homeomorph.prodCongr, hg]
      cases label false <;> rfl
    have hstart : (hamiltonZeroAnnulusTargetMap alpha beta theta).comp f = u := by
      apply ContinuousMap.ext
      intro x
      apply (Q0).injective
      rw [ContinuousMap.comp_apply, hamiltonZeroAnnulusTargetMap_coordinates]
      exact Prod.ext (Prod.ext (hf x) (hphase x).symm) (hnormal x)
    obtain ⟨T⟩ := Hc
    exact Or.inr ⟨hsame, c, hc, ⟨T⟩, q, hq, hqtarget,
      ⟨(hamiltonZeroAnnulusCoordinateHomotopy T theta alpha beta).cast hstart rfl⟩⟩

end PoincareMT.M76

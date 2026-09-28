import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.ComponentRim
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.CylinderLift
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.NormalizedMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Annuli.Coordinates










set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "C32" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_source_annulus_rim_lift
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (phi psi : C(H0, H0)) {R A : Set X0}
    (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {theta other : C0} (hne : theta ≠ other)
    (hreg : HamiltonZeroSecondCoordinateRegularity e R phi theta)
    {a b : ℝ}
    (hN : PLDomain e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {other})))
    (hcover : IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    {S : Set X0} (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S, connectedComponentIn
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}) x = S)
    (H : Ann ≃ₜ S)
    (hmark : ∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
      (H z : X0) ∈ frontier R)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (halphabeta : alpha < beta)
    (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap psi ⁻¹' {(alpha : C0), (beta : C0)}) :
    ∃ (f : C(Ann, unitInterval × C0)) (label : Bool → Bool) (g : C(C32, C0)),
      (∀ z : Ann, (f z).2 = (Q0 (hamiltonZeroAmbientMap psi (H z))).1.1) ∧
      (∀ z : Ann, (((beta - alpha) * ((f z).1 : ℝ) + alpha : ℝ) : C0) =
        hamiltonZeroCircleMap psi (H z)) ∧
      (∀ side : Bool, ∀ z : C32, f (Dehn.annulusRimPoint side z) =
        (if label side then 1 else 0,
          (Q0 (hamiltonZeroAmbientMap psi (H (Dehn.annulusRimPoint side z)))).1.1)) ∧
      (∀ z : C32, g z =
        (Q0 (hamiltonZeroAmbientMap psi (H (Dehn.annulusRimPoint false z)))).1.1) ∧
      IsCoveringMap g ∧
      (∀ side : Bool, IsCoveringMap (fun z : C32 => (f (Dehn.annulusRimPoint side z)).2)) ∧
      ∃ Hrim : C32 ≃ₜ C32, ∃ L : (ContinuousMap.id C32).Homotopy (Hrim : C(C32, C32)),
        ∀ t z, g (L (t, z)) = (f (Dehn.annulusCylinderHomeomorph (t, z))).2 := by
  obtain ⟨f, label, hf, hnormal, hlabels⟩ :=
    exists_hamiltonZero_normalized_annulus_map psi halpha halphabeta hbeta hR hRfront
      (fun _ hx => (hS hx).1) H hmark
  have hrims (side : Bool) :
      IsCoveringMap (fun z : C32 => (f (Dehn.annulusRimPoint side z)).2) := by
    simp only [hf]
    exact hamiltonZero_compressed_annulus_rim_circle_covering e phi psi heR hA hAR
      hfixed hne hreg hN hfront hcover hS hcomponent H hmark side
  let g : C(C32, C0) := ⟨fun z => (f (Dehn.annulusRimPoint false z)).2,
    (f.continuous.comp (Dehn.continuous_annulusRimPoint false)).snd⟩
  let q : C(unitInterval × C32, C0) :=
    ⟨fun z => (f (Dehn.annulusCylinderHomeomorph z)).2,
      (f.continuous.comp Dehn.annulusCylinderHomeomorph.continuous).snd⟩
  have hzero (z : C32) : q (0, z) = g z := by
    change (f (Dehn.annulusCylinderHomeomorph (0, z))).2 = _
    rw [Dehn.annulusCylinderHomeomorph_zero]
    rfl
  have hone : IsCoveringMap (fun z => q (1, z)) := by
    simpa only [q, ContinuousMap.coe_mk, Dehn.annulusCylinderHomeomorph_one] using hrims true
  obtain ⟨Hrim, L, hlift⟩ := IsCoveringMap.exists_addCircle_cylinder_lift_homeomorph
    (by norm_num : 0 < 4 * (8 : ℝ)) (by norm_num : 0 < p) (hrims false) q hzero hone
  exact ⟨f, label, g, hf, hnormal, hlabels, fun z => hf _, hrims false, hrims,
    Hrim, L, hlift⟩

end PoincareConjecture.M76

import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.FoldedMarkedStraightening
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.SourceRimLift

/-!
# A covering-coordinate normal form for an actual source annulus

The compressed source geometry constructs the complete rim coverings and
their relative lift. Both opposite and equal rim labels admit an endpoint
given by a covering of the cylinder, realized between the selected target
normal endpoints. Equal endpoints retain the full circle-fibration formula.
-/

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_source_annulus_normal_form
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi psi : C(H0, H0))
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    {R A : Set X0} (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
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
    (H : Ann ≃ₜ S) (j : ℝ × ℝ → X0) (hj : PolyhedralPLInCharts e j Ann)
    (hJ : ∀ z : Ann, j z = (H z : X0))
    (hmark : ∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
      (H z : X0) ∈ frontier R)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (halphabeta : alpha < beta)
    (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap psi ⁻¹' {(alpha : C0), (beta : C0)}) :
    let u : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap psi (j z),
      (hamiltonZeroAmbientMap psi).continuous.comp hj.continuousOn.domRestrict⟩
    ∃ delta0 ∈ ({alpha, beta} : Set ℝ), ∃ delta1 ∈ ({alpha, beta} : Set ℝ),
      ∃ c : C(Ann, unitInterval × C0), IsCoveringMap c ∧
        ∃ q : ℝ × ℝ → X0, PolyhedralPLInCharts d q Ann ∧
          (∀ z : Ann, q z = hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) ∧
          Nonempty (u.HomotopyRel
            ((hamiltonZeroAnnulusTargetMap delta0 delta1 theta).comp c) Dehn.annulusRims) := by
  intro u
  obtain ⟨f, label, g, hf, hnormal, hlabels, hg, hgc, _, Hrim, L, hlift⟩ :=
    exists_hamiltonZero_source_annulus_rim_lift e phi psi heR hA hAR hfixed hne hreg
      hN hfront hcover hS hcomponent H hmark halpha halphabeta hbeta hR hRfront
  have hphase (z : Ann) : (Q0 (hamiltonZeroAmbientMap psi (j z))).1.2 = theta := by
    rw [hJ, ← hamiltonZeroSecondCircleMap_ambient]
    exact (hS (H z).property).2
  have hf' (z : Ann) : (f z).2 = (Q0 (hamiltonZeroAmbientMap psi (j z))).1.1 := by
    rw [hJ]
    exact hf z
  have hn' (z : Ann) : (((beta - alpha) * ((f z).1 : ℝ) + alpha : ℝ) : C0) =
      (Q0 (hamiltonZeroAmbientMap psi (j z))).2 := by
    rw [hJ]
    exact hnormal z
  have hg' (z : Circle) : g z =
      (Q0 (hamiltonZeroAmbientMap psi (j (Dehn.annulusRimPoint false z)))).1.1 := by
    rw [hJ]
    exact hg z
  have hlabels' (side : Bool) (z : Circle) :
      (f (Dehn.annulusRimPoint side z)).1 = if label side then 1 else 0 :=
    congrArg Prod.fst (hlabels side z)
  rcases exists_hamiltonZero_annulus_marked_or_folded hd hpsi hj halpha halphabeta hbeta
      hphase f label hf' hn' hlabels' g hg' hgc Hrim L hlift with hfold | hmarked
  · let delta : ℝ := if label false then beta else alpha
    have hdelta : delta ∈ ({alpha, beta} : Set ℝ) := by
      dsimp [delta]
      cases label false <;> simp
    have hdeltaArc : delta ∈ Icc alpha beta := by
      rcases hdelta with h | h <;> rw [h] <;>
        exact ⟨by linarith, by linarith⟩
    have hrim (side : Bool) (z : Circle) :
        (Q0 (hamiltonZeroAmbientMap psi (j (Dehn.annulusRimPoint side z)))).2 = (delta : C0) := by
      rw [← hn', hlabels']
      have hlabel : label side = label false := by
        cases side
        · rfl
        · exact hfold.1.symm
      rw [hlabel]
      dsimp [delta]
      cases label false <;> simp
    have hslab (z : Ann) : (Q0 (hamiltonZeroAmbientMap psi (j z))).2 ∈
        AddCircle.closedIntervalArc p alpha beta := by
      rw [hJ]
      exact hR (hS (H z).property).1
    obtain ⟨c, hc, q, hq, hqval, hhom⟩ :=
      exists_hamiltonZero_folded_marked_annulus_covering hd hpsi hj halpha hbeta hdeltaArc
        hphase hslab hrim f hf' g hg' hgc Hrim L hlift
    exact ⟨delta, hdelta, delta, hdelta, c, hc, q, hq, hqval, hhom⟩
  · obtain ⟨_, c, hc, _, q, hq, hqval, hhom⟩ := hmarked
    exact ⟨alpha, by simp, beta, by simp, c, hc, q, hq, hqval, hhom⟩

end PoincareMT.M76

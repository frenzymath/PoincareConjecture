import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.FiniteDisplacementExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.RelativeDisplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.MarkedDisplacementExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.AmbientDisplacement
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.NormalDisplacementBound
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.RetainedArcDisplacement

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_finite_marked_annulus_installation
    {ι κ η : Type*} [Fintype η]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
    (j : η → (ℝ × ℝ) → X0) (hj : ∀ i, PolyhedralPLInCharts e (j i) Ann)
    (hji : ∀ i, Topology.IsEmbedding (fun z : Ann => j i z))
    (hjR : ∀ i, MapsTo (j i) Ann R)
    (hrim : ∀ i, ∀ z : Ann,
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔ j i z ∈ frontier R)
    (hdis : Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)))
    (q : η → (ℝ × ℝ) → X0) (hq : ∀ i, PolyhedralPLInCharts d (q i) Ann)
    (v : η → C(Ann, X0)) (hv : ∀ i, ∀ z : Ann, q i z = v i z)
    (hphase : ∀ i, ∀ z : Ann, (Q0 (v i z)).1.2 =
      (Q0 (hamiltonZeroAmbientMap phi (j i z))).1.2)
    (H : ∀ i, (⟨fun z : Ann => hamiltonZeroAmbientMap phi (j i z),
      (hamiltonZeroAmbientMap phi).continuous.comp (hj i).continuousOn.domRestrict⟩ :
      C(Ann, X0)).HomotopyRel (v i) Dehn.annulusRims)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (hab : alpha ≤ beta) (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hvArc : ∀ i, ∀ z : Ann, (Q0 (v i z)).2 ∈ AddCircle.closedIntervalArc p alpha beta) :
    ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      hamiltonZeroSecondCircleMap psi = hamiltonZeroSecondCircleMap phi ∧
      (∀ i, ∀ z : Ann, hamiltonZeroAmbientMap psi (j i z) = v i z) ∧
      (R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap psi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.2 = hamiltonZeroSecondCircleMap phi x) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let : Fact (0 < p) := ⟨by norm_num⟩
  let u (i : η) : C(Ann, X0) := ⟨fun z => hamiltonZeroAmbientMap phi (j i z),
    (hamiltonZeroAmbientMap phi).continuous.comp (hj i).continuousOn.domRestrict⟩
  have hex (i : η) := exists_hamiltonZero_relative_annulus_displacement
    hd hphi (hj i) (hq i) (hv i) (hphase i) (H i)
  choose w hw hwphase hwrim hwval using hex
  have hwdepth (i : η) (z : Ann)
      (hz : depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1) : w i z = 0 := by
    apply hwrim i z
    rcases hz with hz | hz
    · exact Or.inl ((Dehn.range_annulusRimPoint false).symm.subset hz)
    · exact Or.inr ((Dehn.range_annulusRimPoint true).symm.subset hz)
  obtain ⟨W, hW, hWbase, hWprotected, hWphase⟩ :=
    exists_original_finite_annulus_displacement_extension e heR j hj hji hjR hrim hdis
      w hw (fun i z hz => hwphase i ⟨z, hz⟩) hwdepth
  let wn (i : η) : C(Ann, ℝ) := ⟨fun z => w i z 2,
    (continuous_apply 2).comp (hw i).continuousOn.domRestrict⟩
  have hwn (i : η) (z : Ann) : (wn i z : C0) = (Q0 (v i z)).2 - (Q0 (u i z)).2 := by
    have h := congrArg (fun x : X0 => (Q0 x).2) ((hwval i z).trans (hv i z))
    rw [hamiltonZeroTargetVectorTranslation_coordinates] at h
    exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h)
  have hnBound (i : η) := hamiltonZero_annulus_normal_displacement_bound
    (u i) (v i) halpha hab hbeta (fun z => hR (hjR i z.property))
    (hvArc i) (wn i) (hwn i) (fun z hz => congrFun (hwrim i z hz) 2)
  obtain ⟨V, hVPL, _, hVphase, _, hVzero, _, hVsame, hVarc⟩ :=
    exists_hamiltonZero_retained_arc_displacement hd hphi heR halpha hab hbeta hR
      W hW hWphase hWprotected
  have hVbase (i : η) (z : Ann) : V (j i z) = w i z := by
    rw [hVsame (j i z) (hjR i z.property) (by
      rw [hWbase i z]
      exact (hnBound i z).2), hWbase i z]
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
  · intro i z
    rw [hformula, hVbase]
    exact (hwval i z).trans (hv i z)
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

end PoincareConjecture.M76

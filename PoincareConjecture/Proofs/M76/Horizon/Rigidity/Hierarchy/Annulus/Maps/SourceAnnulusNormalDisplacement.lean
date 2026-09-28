import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Coverings.ThirdPhasePLArcs
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.RelativeDisplacement










set_option autoImplicit false
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



def HamiltonZeroMarkedAnnulusPLArcFibers
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0)
    (j : ℝ × ℝ → X0) (c : C(Ann, unitInterval × C0)) : Prop :=
  ∀ xi : C0, ∃ (n : ℕ) (arc : Fin n → C(unitInterval, Ann))
      (param : Fin n → ℝ → ℝ × ℝ),
    (∀ i, Topology.IsEmbedding (arc i)) ∧
    (∀ i, FinitePiecewiseAffineOn (param i) (Icc (0 : ℝ) 1)) ∧
    (∀ i (t : unitInterval), param i t = (arc i t : ℝ × ℝ)) ∧
    (∀ i, PolyhedralPLInCharts e (j ∘ param i) (Icc (0 : ℝ) 1)) ∧
    Pairwise (fun i k => Disjoint (range (arc i)) (range (arc k))) ∧
    (⋃ i, range (arc i)) = {z | (c z).2 = xi} ∧
    ∀ i t, j (arc i t) ∈ frontier R ↔ t = 0 ∨ t = 1



def HamiltonZeroInstalledAnnulusPLArcFibers
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0)
    (j : ℝ × ℝ → X0) (chi : C(H0, H0)) (c : C(Ann, unitInterval × C0)) : Prop :=
  ∀ xi : C0, ∃ (n : ℕ) (arc : Fin n → C(unitInterval, Ann))
      (param : Fin n → ℝ → ℝ × ℝ),
    (∀ i, Topology.IsEmbedding (arc i)) ∧
    (∀ i, FinitePiecewiseAffineOn (param i) (Icc (0 : ℝ) 1)) ∧
    (∀ i (t : unitInterval), param i t = (arc i t : ℝ × ℝ)) ∧
    (∀ i, PolyhedralPLInCharts e (j ∘ param i) (Icc (0 : ℝ) 1)) ∧
    Pairwise (fun i k => Disjoint (range (arc i)) (range (arc k))) ∧
    (⋃ i, range (arc i)) = {z | (c z).2 = xi} ∧
    (⋃ i, range (fun t : unitInterval => j (arc i t))) =
      j '' Ann ∩ {x | (Q0 (hamiltonZeroAmbientMap chi x)).1.1 = xi} ∧
    ∀ i t, j (arc i t) ∈ frontier R ↔ t = 0 ∨ t = 1

theorem HamiltonZeroMarkedAnnulusPLArcFibers.installed
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3} {R : Set X0}
    {j : ℝ × ℝ → X0} {c : C(Ann, unitInterval × C0)}
    (harcs : HamiltonZeroMarkedAnnulusPLArcFibers e R j c)
    (chi : C(H0, H0)) {delta0 delta1 : ℝ} {theta : C0}
    (hformula : ∀ z : Ann, hamiltonZeroAmbientMap chi (j z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 theta (c z)) :
    HamiltonZeroInstalledAnnulusPLArcFibers e R j chi c := by
  intro xi
  obtain ⟨n, arc, param, hi, hPL, hparam, hsourcePL, hdis, hwhole, hends⟩ := harcs xi
  have hphase (z : Ann) : (Q0 (hamiltonZeroAmbientMap chi (j z))).1.1 = (c z).2 := by
    rw [hformula, hamiltonZeroAnnulusTargetMap_coordinates]
  refine ⟨n, arc, param, hi, hPL, hparam, hsourcePL, hdis, hwhole, ?_, hends⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, t, rfl⟩ := mem_iUnion.mp hx
    refine ⟨⟨arc i t, (arc i t).property, rfl⟩, ?_⟩
    change (Q0 (hamiltonZeroAmbientMap chi (j (arc i t)))).1.1 = xi
    rw [hphase]
    exact hwhole.subset (mem_iUnion.mpr ⟨i, t, rfl⟩)
  · rintro ⟨⟨z, hz, rfl⟩, hxi⟩
    have hzphase : (c ⟨z, hz⟩).2 = xi := (hphase ⟨z, hz⟩).symm.trans hxi
    obtain ⟨i, t, ht⟩ := mem_iUnion.mp (hwhole.symm.subset hzphase)
    exact mem_iUnion.mpr ⟨i, t, congrArg (fun y : Ann => j y) ht⟩

theorem exists_hamiltonZero_source_annulus_normal_displacement
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
    ∃ (q : ℝ × ℝ → X0) (v : C(Ann, X0)) (w : ℝ × ℝ → V3),
      PolyhedralPLInCharts d q Ann ∧ (∀ z : Ann, q z = v z) ∧
      FinitePiecewiseAffineOn w Ann ∧
      (∀ z : Ann, w z 1 = 0) ∧
      (∀ z : Ann, z ∈ Dehn.annulusRims → w z = 0) ∧
      (∀ z : Ann, hamiltonZeroTargetVectorTranslation (w z, u z) = q z) ∧
      Nonempty (u.HomotopyRel v Dehn.annulusRims) ∧
      (∀ z : Ann, (Q0 (v z)).1.2 = theta) ∧
      ∃ delta0 ∈ ({alpha, beta} : Set ℝ), ∃ delta1 ∈ ({alpha, beta} : Set ℝ),
        ∃ c : C(Ann, unitInterval × C0), IsCoveringMap c ∧
          v = (hamiltonZeroAnnulusTargetMap delta0 delta1 theta).comp c ∧
          HamiltonZeroMarkedAnnulusPLArcFibers e R j c := by
  intro u
  obtain ⟨delta0, hdelta0, delta1, hdelta1, c, hc, q, hq, hqval, ⟨Hv⟩, harcs⟩ :=
    exists_hamiltonZero_source_annulus_normal_form_with_PL_arcs hd phi psi hpsi heR hA hAR
      hfixed hne hreg hN hfront hcover hS hcomponent H j hj hJ hmark
      halpha halphabeta hbeta hR hRfront
  let v := (hamiltonZeroAnnulusTargetMap delta0 delta1 theta).comp c
  have hv (z : Ann) : q z = v z := hqval z
  have htheta (z : Ann) : (Q0 (v z)).1.2 = theta :=
    congrArg (fun x : (C0 × C0) × C0 => x.1.2)
      (hamiltonZeroAnnulusTargetMap_coordinates delta0 delta1 theta (c z))
  have hphase (z : Ann) : (Q0 (hamiltonZeroAmbientMap psi (j z))).1.2 = theta := by
    rw [hJ, ← hamiltonZeroSecondCircleMap_ambient]
    exact (hS (H z).property).2
  obtain ⟨w, hw, hwphase, hwrims, hwval⟩ :=
    exists_hamiltonZero_relative_annulus_displacement hd hpsi hj hq hv
      (fun z => (htheta z).trans (hphase z).symm) Hv
  exact ⟨q, v, w, hq, hv, hw, hwphase, hwrims, hwval, ⟨Hv⟩, htheta,
    delta0, hdelta0, delta1, hdelta1, c, hc, rfl, harcs⟩

end PoincareConjecture.M76

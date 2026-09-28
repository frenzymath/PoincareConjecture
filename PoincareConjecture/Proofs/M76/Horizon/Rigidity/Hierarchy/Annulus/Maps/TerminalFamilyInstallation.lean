import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Models.WholeComponentFamily
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.SourceAnnulusNormalDisplacement
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.FiniteMarkedInstallation











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

theorem exists_hamiltonZero_terminal_annulus_installation
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi psi : C(H0, H0))
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    (Fpsi : (ContinuousMap.id H0).HomotopyRel psi B0)
    {R A : Set X0} (heR : PLDomain e R) (hA : IsCompact A) (hAR : A ⊆ interior R)
    (hfixed : ∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0))
    (geometry : HamiltonZeroSecondPhaseGeometry e R psi a b)
    (hcover : ∀ theta ∈ ({a, b} : Set ℝ),
      IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta))
    (hterminal : ∀ theta ∈ ({a, b} : Set ℝ), ∀ T : Set X0, T.Nonempty →
      T ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)} →
      (∀ x ∈ T, connectedComponentIn
        (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}) x = T) →
      (T ∩ frontier R).Nonempty)
    {cut alpha beta : ℝ} (halpha : cut < alpha) (halphabeta : alpha < beta)
    (hbeta : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap psi ⁻¹' {(alpha : C0), (beta : C0)}) :
    ∃ (chi : C(H0, H0)) (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → ℝ × ℝ → X0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
      Nonempty (psi.HomotopyRel chi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
      hamiltonZeroSecondCircleMap chi = hamiltonZeroSecondCircleMap psi ∧
      R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
      (∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Ann) =
        R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {((if s then b else a : ℝ) : C0)}) ∧
      Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)) ∧
      (∀ i, PolyhedralPLInCharts e (j i) Ann ∧
        Topology.IsEmbedding (fun z : Ann => j i z) ∧
        (∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
          j i z ∈ frontier R) ∧
        (∃ delta0 ∈ ({alpha, beta} : Set ℝ), ∃ delta1 ∈ ({alpha, beta} : Set ℝ),
          ∃ c : C(Ann, unitInterval × C0), IsCoveringMap c ∧
            (∀ z : Ann, hamiltonZeroAmbientMap chi (j i z) =
              hamiltonZeroAnnulusTargetMap delta0 delta1
                ((if i.1 then b else a : ℝ) : C0) (c z)) ∧
            HamiltonZeroInstalledAnnulusPLArcFibers e R (j i) chi c)) ∧
      ∃ G : (hamiltonZeroAmbientMap psi).HomotopyRel
          (hamiltonZeroAmbientMap chi) (interior R)ᶜ,
        (∀ t x, (Q0 (G (t, x))).1.2 = (Q0 (hamiltonZeroAmbientMap psi x)).1.2) ∧
        ∀ t x, x ∈ R → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta := by
  classical
  let theta (s : Bool) : ℝ := if s then b else a
  have htheta (s : Bool) : theta s ∈ ({a, b} : Set ℝ) := by cases s <;> simp [theta]
  have habC : (a : C0) ≠ (b : C0) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)).mp h)
  have hne (s : Bool) : (theta s : C0) ≠ (theta (!s) : C0) := by
    cases s
    · exact habC
    · exact habC.symm
  have hfamily := exists_hamiltonZero_terminal_finite_annulus_family e phi psi heR hA hAR
    hfixed ha hab hb hreg geometry hcover hterminal
  choose n T hT hdis hprops using (fun s : Bool => hfamily (theta s) (htheta s))
  let I := Σ s : Bool, Fin (n s)
  let S (i : I) := T i.1 i.2
  have hS (i : I) : S i ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta i.1 : C0)} := by
    rw [← hT i.1]
    exact subset_iUnion (T i.1) i.2
  choose H j hj hJ hmark using (fun i : I => (hprops i.1 i.2).2.2.2)
  have himage (i : I) : j i '' Ann = S i := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hJ i ⟨z, hz⟩]
      exact (H i ⟨z, hz⟩).property
    · intro hx
      refine ⟨H i |>.symm ⟨x, hx⟩, (H i |>.symm ⟨x, hx⟩).property, ?_⟩
      rw [hJ]
      exact congrArg Subtype.val ((H i).apply_symm_apply ⟨x, hx⟩)
  have hji (i : I) : Topology.IsEmbedding (fun z : Ann => j i z) := by
    have hh : (fun z : Ann => j i z) = fun z => (H i z : X0) := funext (hJ i)
    rw [hh]
    exact Topology.IsEmbedding.subtypeVal.comp (H i).isEmbedding
  have hjR (i : I) : MapsTo (j i) Ann R := by
    intro z hz
    exact (hS i (himage i ▸ (show j i z ∈ j i '' Ann from ⟨z, hz, rfl⟩))).1
  have hrim (i : I) (z : Ann) :
      depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔ j i z ∈ frontier R := by
    rw [hJ]
    exact hmark i z
  have hdisjoint : Pairwise (fun i k : I => Disjoint (j i '' Ann) (j k '' Ann)) := by
    intro i k hik
    rw [himage, himage]
    rcases i with ⟨s, i⟩
    rcases k with ⟨t, k⟩
    by_cases hst : s = t
    · subst t
      exact hdis s (fun h => hik (by cases h; rfl))
    · apply disjoint_left.mpr
      intro x hxi hxk
      have hi := (hS ⟨s, i⟩ hxi).2
      have hk := (hS ⟨t, k⟩ hxk).2
      have heq : (theta s : C0) = (theta t : C0) := hi.symm.trans hk
      cases s <;> cases t
      · exact hst rfl
      · exact habC heq
      · exact habC heq.symm
      · exact hst rfl
  have hex (i : I) := exists_hamiltonZero_source_annulus_normal_displacement hd phi psi hpsi heR hA hAR
    hfixed (hne i.1) (hreg _ (htheta i.1)) (geometry.slabs false).1
    (show frontier (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b) ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta i.1 : C0)}) ∪
          (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta (!i.1) : C0)})) from by
      cases hi : i.1
      · simpa only [hi, theta, Bool.not_false, Bool.false_eq_true, if_false, if_true] using
          (geometry.slabs false).2.1
      · simpa only [hi, theta, Bool.not_true, Bool.false_eq_true, if_false, if_true, union_comm] using
          (geometry.slabs false).2.1)
    (hcover _ (htheta i.1)) (hS i) (hprops i.1 i.2).2.2.1
    (H i) (j i) (hj i) (hJ i) (hmark i) halpha halphabeta hbeta hR hRfront
  choose q v w hq hqv hw hw1 hwrim hwval hhom hsecond halt using hex
  have hphase (i : I) (z : Ann) : (Q0 (v i z)).1.2 =
      (Q0 (hamiltonZeroAmbientMap psi (j i z))).1.2 := by
    rw [hsecond]
    symm
    rw [← hamiltonZeroSecondCircleMap_ambient]
    exact (hS i (himage i ▸ (show j i z ∈ j i '' Ann from ⟨z, z.property, rfl⟩))).2
  have hvArc (i : I) (z : Ann) : (Q0 (v i z)).2 ∈ AddCircle.closedIntervalArc p alpha beta := by
    obtain ⟨delta0, hdelta0, delta1, hdelta1, c, _, hvalue, _⟩ := halt i
    rw [hvalue]
    change (Q0 (hamiltonZeroAnnulusTargetMap delta0 delta1 _ (c z))).2 ∈ _
    rw [hamiltonZeroAnnulusTargetMap_coordinates]
    refine ⟨(delta1 - delta0) * ((c z).1 : ℝ) + delta0, ?_, rfl⟩
    have ht := (c z).1.property
    rcases hdelta0 with rfl | rfl <;> rcases hdelta1 with rfl | rfl <;>
      constructor <;> nlinarith [ht.1, ht.2]
  obtain ⟨chi, hchi, Hchi, Fchi, hsecondchi, hvalue, hRchi, G, hGsecond, hGarc⟩ :=
    exists_hamiltonZero_finite_marked_annulus_installation hd hpsi Fpsi heR
      j hj hji hjR hrim hdisjoint q hq v hqv hphase (fun i => (hhom i).some)
      halpha halphabeta.le hbeta hR hvArc
  refine ⟨chi, n, j, hchi, Hchi, Fchi, hsecondchi, hRchi, ?_, hdisjoint, ?_, G, hGsecond, hGarc⟩
  · intro s
    simp_rw [himage, hsecondchi]
    exact hT s
  · intro i
    refine ⟨hj i, hji i, hrim i, ?_⟩
    obtain ⟨delta0, hdelta0, delta1, hdelta1, c, hc, heq, harcs⟩ := halt i
    have hformula (z : Ann) : hamiltonZeroAmbientMap chi (j i z) =
        hamiltonZeroAnnulusTargetMap delta0 delta1 (theta i.1) (c z) := by
      rw [hvalue, heq]
      rfl
    exact ⟨delta0, hdelta0, delta1, hdelta1, c, hc, hformula,
      harcs.installed chi hformula⟩

end PoincareConjecture.M76

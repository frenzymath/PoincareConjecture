import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SourceCirclePhases
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.Elimination
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.IrreducibleSlabs

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_boundary_meeting_second_hierarchy
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (hI : IsPLIrreducible e R)
    {cut alpha beta : ℝ}
    (ha : cut < alpha) (hab : alpha ≤ beta) (hb : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X0)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, ∀ t ∈ Icc (-r) r,
      (Q0 (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0)) ∧
      ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
        (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
        hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
        (∀ theta : C0,
          (frontier R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}).Nonempty) ∧
        HamiltonZeroSecondPhaseGeometry e R psi a b ∧
        (∀ theta ∈ ({a, b} : Set ℝ), ∀ S : Set X0, S.Nonempty →
          S ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)} →
          (∀ x ∈ S, connectedComponentIn
            (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}) x = S) →
          (S ∩ frontier R).Nonempty) ∧
        ∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) := by
  obtain ⟨a, ha', b, hb', hreg, eta, A, hA, hAR, hfixedEta, hnormalEta,
      heta, ⟨Heta⟩, ⟨Feta⟩, ⟨HextEta⟩, hslabs, hphases⟩ :=
    exists_hamiltonZero_injective_circle_second_hierarchy_with_regular_phases
      e d hd phi hphi F0 hI.1 ha hab hb hR hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  have geometry : HamiltonZeroSecondPhaseGeometry e R eta a b := by
    refine ⟨hslabs, ?_⟩
    intro s hs x
    refine ⟨?_, ((hphases s hs).2 x).2.1⟩
    let inclusion : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
    let phaseInclusion := ContinuousMap.inclusion
      (inter_subset_left : R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(s : C0)} ⊆ R)
    change Function.Injective (FundamentalGroup.map (inclusion.comp phaseInclusion) x)
    rw [FundamentalGroup.map_comp]
    exact (hinjR (phaseInclusion x)).comp (((hphases s hs).2 x).1)
  obtain ⟨psi, B, hB, hBR, hfixedPsi, hnormalPsi, hpsi, ⟨Hpsi⟩, Fpsi,
      ⟨HextPsi⟩, geom, hcomponents⟩ :=
    exists_hamiltonZero_second_phases_without_closed_components e d hd phi eta heta Feta
      hI hA hAR hfixedEta (by linarith [ha'.1]) (by linarith [ha'.2, hb'.1])
        (by linarith [hb'.2]) hreg geometry
  have hsupport : A ∪ B ⊆ interior R := union_subset hAR hBR
  have hfixed (x : X0) (hx : x ∉ A ∪ B) :
      hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x :=
    (hfixedPsi x (fun h => hx (Or.inr h))).trans
      (hfixedEta x (fun h => hx (Or.inl h)))
  have hboundary : ∀ theta : C0,
      (frontier R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {theta}).Nonempty := by
    intro theta
    obtain ⟨x, hxfront, hxphase⟩ := hamiltonZero_installed_second_boundary_levels_nonempty
      hK hne phi c hzero g hg (fun x => hproduct x 0 (by constructor <;> linarith)) theta
    refine ⟨x, hxfront, ?_⟩
    change hamiltonZeroSecondCircleMap psi x = theta
    rw [hamiltonZeroSecondCircleMap_ambient,
      hfixed x (fun hx => hxfront.2 (hsupport hx)), ← hamiltonZeroSecondCircleMap_ambient]
    exact hxphase
  refine ⟨a, ha', b, hb', hreg, psi, A ∪ B, hA.union hB, hsupport, hfixed,
    hnormalPsi.trans hnormalEta, hpsi, ⟨Heta.trans Hpsi⟩, Fpsi,
    ⟨HextEta.trans HextPsi⟩, hboundary, geom, hcomponents, ?_⟩
  apply isPLIrreducible_hamiltonZero_complementary_second_slabs psi hI
    (fun side => ⟨(geom.slabs side).1, (geom.slabs side).2.1⟩)
  intro theta htheta x hx
  exact hcomponents theta htheta
    (connectedComponentIn (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}) x)
    ⟨x, mem_connectedComponentIn hx⟩ (connectedComponentIn_subset _ _)
    (fun y hy => (connectedComponentIn_eq hy).symm)

end PoincareConjecture.M76

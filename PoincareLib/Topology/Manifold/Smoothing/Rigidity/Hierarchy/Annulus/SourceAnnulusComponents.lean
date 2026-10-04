import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SourceBoundaryPhases
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Spheres.TerminalAnnuli

/-!
# Whole annulus components of the second source hierarchy

The installed covering, original regular levels, and irreducible retained
region construct both compressed phase families. Every closed component is
removed; the surviving components are original-atlas PL annuli with precisely
their two rims on the retained boundary. No component model or group property
is supplied to the construction.
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
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_source_annulus_components
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
        (∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) ∧
        ∀ theta ∈ ({a, b} : Set ℝ), ∀ S : Set X0, S.Nonempty →
          S ⊆ R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)} →
          (∀ x ∈ S, connectedComponentIn
            (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}) x = S) →
          ∃ H : squareAnnulus 8 1 ≃ₜ S, ∃ f : (ℝ × ℝ) → X0,
            PolyhedralPLInCharts e f (squareAnnulus 8 1) ∧
            (∀ z : squareAnnulus 8 1, f z = (H z : X0)) ∧
            ∀ z : squareAnnulus 8 1,
              depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
                (H z : X0) ∈ frontier R := by
  obtain ⟨a, ha', b, hb', hreg, psi, A, hA, hAR, hfixed, hnormal,
      hpsi, Hpsi, Fpsi, Hext, hboundary, geom, hcomponents, hcuts⟩ :=
    exists_hamiltonZero_boundary_meeting_second_hierarchy e d hd phi hphi F0 hI
      ha hab hb hR hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  refine ⟨a, ha', b, hb', hreg, psi, A, hA, hAR, hfixed, hnormal,
    hpsi, Hpsi, Fpsi, Hext, hboundary, geom, hcuts, ?_⟩
  exact exists_hamiltonZero_terminal_component_annuli e phi psi hI.1 hA hAR hfixed
    (by linarith [ha'.1]) (by linarith [ha'.2, hb'.1]) (by linarith [hb'.2]) hreg geom
    (fun theta _ => hamiltonZero_installed_boundary_rim_circle_covering
      hK phi hr c hi hzero g hg hproduct (theta : C0))
    hcomponents

end PoincareMT.M76

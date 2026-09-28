import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SourceBoundaryPhases
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.TerminalFamilyInstallation
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.InstalledGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.InstalledSlabInjection









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

theorem exists_hamiltonZero_source_annulus_family_installation
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (hI : IsPLIrreducible e R)
    {cut alpha beta : ℝ}
    (ha : cut < alpha) (hab : alpha < beta) (hb : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
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
      ∃ (chi : C(H0, H0)) (n : Bool → ℕ) (j : (Σ s : Bool, Fin (n s)) → ℝ × ℝ → X0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
        Nonempty (phi.HomotopyRel chi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap chi) (interior R)ᶜ) ∧
        R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        HamiltonZeroSecondPhaseGeometry e R chi a b ∧
        (∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) ∧
        (∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          ∀ x : N, Function.Injective
            (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ⊆ R)) x)) ∧
        (∀ theta : C0, (frontier R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {theta}).Nonempty) ∧
        (∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Ann) =
          R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {((if s then b else a : ℝ) : C0)}) ∧
        Pairwise (fun i k => Disjoint (j i '' Ann) (j k '' Ann)) ∧
        ∀ i, PolyhedralPLInCharts e (j i) Ann ∧
          Topology.IsEmbedding (fun z : Ann => j i z) ∧
          (∀ z : Ann, depth 8 (z : ℝ × ℝ) = -1 ∨ depth 8 (z : ℝ × ℝ) = 1 ↔
            j i z ∈ frontier R) ∧
          (∃ delta0 ∈ ({alpha, beta} : Set ℝ), ∃ delta1 ∈ ({alpha, beta} : Set ℝ),
            ∃ f : C(Ann, unitInterval × C0), IsCoveringMap f ∧
              (∀ z : Ann, hamiltonZeroAmbientMap chi (j i z) =
                hamiltonZeroAnnulusTargetMap delta0 delta1
                  ((if i.1 then b else a : ℝ) : C0) (f z)) ∧
              HamiltonZeroInstalledAnnulusPLArcFibers e R (j i) chi f) := by
  obtain ⟨a, ha', b, hb', hreg, psi, A, hA, hAR, hfixed, hnormal,
      hpsi, ⟨Hpsi⟩, ⟨Fpsi⟩, ⟨Hext⟩, hboundary, geometry, hterminal, hcuts⟩ :=
    exists_hamiltonZero_boundary_meeting_second_hierarchy e d hd phi hphi F0 hI
      ha hab.le hb hR hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  have hRpsi : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [hnormal]
    exact hR
  have hRfrontPsi : frontier R ⊆ hamiltonZeroCircleMap psi ⁻¹' {(alpha : C0), (beta : C0)} := by
    rw [hnormal]
    exact hRfront
  have hcover (theta : ℝ) (_ : theta ∈ ({a, b} : Set ℝ)) :
      IsCoveringMap (hamiltonZeroSecondPhaseCircleMap phi (frontier R) theta) :=
    hamiltonZero_installed_boundary_rim_circle_covering
      hK phi hr c hi hzero g hg hproduct (theta : C0)
  obtain ⟨chi, n, j, hchi, ⟨Hchi⟩, ⟨Fchi⟩, hsecond, hRchi, hfamily,
      hdis, halternatives, G, _, _⟩ :=
    exists_hamiltonZero_terminal_annulus_installation hd phi psi hpsi Fpsi hI.1 hA hAR hfixed
      (by linarith [ha'.1]) (by linarith [ha'.2, hb'.1]) (by linarith [hb'.2])
      hreg geometry hcover hterminal ha hab hb hRpsi hRfrontPsi
  have hslabpi := hamiltonZero_installed_second_slabs_pi1_injective
    e phi psi chi hI.1 hA hAR hfixed
    (by linarith [ha'.1]) (by linarith [ha'.2, hb'.1]) (by linarith [hb'.2])
    hreg geometry hsecond
    (hamiltonZero_installed_second_boundary_levels_nonempty hK hne phi c hzero g hg
      (fun x => hproduct x 0 (by constructor <;> linarith)) a)
  refine ⟨a, ha', b, hb', hreg, chi, n, j, hchi, ⟨Hpsi.trans Hchi⟩, ⟨Fchi⟩,
    ⟨Hext.trans G⟩, hRchi,
    geometry.of_secondCircleMap_eq hsecond Fchi ha hab.le hb hRchi,
    ?_, hslabpi, ?_, hfamily, hdis, halternatives⟩
  · intro side
    rw [hsecond]
    exact hcuts side
  · intro theta
    rw [hsecond]
    exact hboundary theta

end PoincareConjecture.M76

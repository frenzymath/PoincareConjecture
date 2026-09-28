import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SourceIncompressiblePhases
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.SecondPhaseGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.IntegerWinding










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

theorem exists_hamiltonZero_injective_circle_second_hierarchy_with_regular_phases
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
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
        (∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
            ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
              (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)})) ∧
          ∀ theta ∈ ({a, b} : Set ℝ),
            let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}
            ∃ hSN : S ⊆ N, ∀ x : S,
              Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x)) ∧
        ∀ theta ∈ ({a, b} : Set ℝ),
          let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}
          S.Nonempty ∧ ∀ x : S,
            Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x) ∧
            Function.Injective (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap psi R theta) x) ∧
            IsCyclic (FundamentalGroup S x) := by
  obtain ⟨a, ha', b, hb', hreg, psi, A, hA, hAR, hfixed, hnormal, hpsi, Hpsi, ⟨Fpsi⟩,
    Hext, hslabs, hphases⟩ :=
    exists_hamiltonZero_incompressible_second_hierarchy_with_regular_phases e d hd phi hphi F0 heR
      hK hne hr c hc hi ho hzero hside g hg hproduct
  have hRpsi : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [hnormal]
    exact hR
  refine ⟨a, ha', b, hb', hreg, psi, A, hA, hAR, hfixed, hnormal, hpsi, Hpsi, ⟨Fpsi⟩,
    Hext, hslabs, ?_⟩
  intro theta htheta
  obtain ⟨hS, hSR⟩ := hphases theta htheta
  refine ⟨hS, fun x => ?_⟩
  have hcircle := hamiltonZeroSecondPhaseCircleMap_pi1_injective_of_region
    psi Fpsi ha hab hb hRpsi theta hinjR hSR x
  let : IsCyclic (FundamentalGroup C0 (hamiltonZeroSecondPhaseCircleMap psi R theta x)) :=
    HamiltonIntervalTorus.circleFundamentalGroup_isCyclic p (by norm_num) _
  exact ⟨hSR x, hcircle, isCyclic_of_injective
    (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap psi R theta) x) hcircle⟩

theorem exists_hamiltonZero_injective_circle_second_hierarchy
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (heR : PLDomain e R)
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
      ∃ (psi : C(H0, H0)) (A : Set X0), IsCompact A ∧ A ⊆ interior R ∧
        (∀ x ∉ A, hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x) ∧
        hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
        (∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
            ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
              (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)})) ∧
          ∀ theta ∈ ({a, b} : Set ℝ),
            let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}
            ∃ hSN : S ⊆ N, ∀ x : S,
              Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x)) ∧
        ∀ theta ∈ ({a, b} : Set ℝ),
          let S := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}
          S.Nonempty ∧ ∀ x : S,
            Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x) ∧
            Function.Injective (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap psi R theta) x) ∧
            IsCyclic (FundamentalGroup S x) := by
  obtain ⟨a, ha', b, hb', _, h⟩ :=
    exists_hamiltonZero_injective_circle_second_hierarchy_with_regular_phases
      e d hd phi hphi F0 heR ha hab hb hR hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  exact ⟨a, ha', b, hb', h⟩

end PoincareConjecture.M76

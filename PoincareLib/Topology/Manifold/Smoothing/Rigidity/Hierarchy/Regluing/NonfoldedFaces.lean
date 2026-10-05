import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.SourceDiskAlternative
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.ThirdPhaseArcs
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.FiniteClosedPartition

/-!
# Successful disk straightening excludes folded annulus faces

The prescribed disk rims already have injective original target maps in the
successful branch. A vertical interval of a folded annulus has constant target
image and lies in one member of the complete finite disk family. Its distinct
endpoints contradict that constructed rim injectivity.
-/

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "Ann" => squareAnnulus 8 1

/-- The successful rectangle extension fixes the whole old disk rim, so its
injectivity also holds for the original ambient map on that literal rim. -/
theorem HamiltonZeroHomeomorphicDiskInstallation.injOn_disk_frontier
    {ι κ η : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {N : Set X0} {phi : C(H0, H0)}
    {j : η → V2 → X0} {theta : η → C0} {alpha beta a b : ℝ}
    (good : HamiltonZeroHomeomorphicDiskInstallation e d N phi j theta alpha beta a b)
    (hrim : ∀ i (z : Disk), j i z ∈ frontier N ↔ (z : V2) ∈ Rim) (i : η) :
    InjOn (hamiltonZeroAmbientMap phi) (j i '' Disk ∩ frontier N) := by
  obtain ⟨v, w, q, E, psi, _, _, _, _, _, _, _, hqi, hqrim, _⟩ := good
  rintro x ⟨⟨z, hz, rfl⟩, hx⟩ y ⟨⟨t, ht, rfl⟩, hy⟩ heq
  have hzrim := (hrim i ⟨z, hz⟩).mp hx
  have htrim := (hrim i ⟨t, ht⟩).mp hy
  have hzt : z = t := hqi i hz ht
    ((hqrim i hzrim).trans (heq.trans (hqrim i htrim).symm))
  exact congrArg (j i) hzt

private theorem endpoints_eq_of_constant_in_finite_injective_cover
    {X Y η : Type*} [TopologicalSpace X] [Finite η]
    (M : η → Set X) (hclosed : ∀ i, IsClosed (M i))
    (hdis : Pairwise (fun i k => Disjoint (M i) (M k)))
    (f : X → Y) (hinj : ∀ i, InjOn f (M i))
    (k : C(unitInterval, X)) (hcover : range k ⊆ ⋃ i, M i)
    (hconstant : ∀ t, f (k t) = f (k 0)) : k 0 = k 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (mem_range_self 0))
  let k' : C(unitInterval, (⋃ i, M i)) :=
    ⟨fun t => ⟨k t, hcover (mem_range_self t)⟩, k.continuous.subtype_mk _⟩
  have hclopen := Poincare.Topology.isClopen_part_of_finite_closed_partition
    M hclosed hdis i
  have hmem (t : unitInterval) : k t ∈ M i :=
    hclopen.map_mem k'.continuous 0 hi t
  exact hinj i (hmem 0) (hmem 1) (hconstant 1).symm

/-- A complete successful disk family forces every adjacent installed annulus
to have opposite normal labels. All injectivity used here comes from `good`. -/
theorem HamiltonZeroHomeomorphicDiskInstallation.normal_labels_ne_of_annulus
    {ι κ η : Type*} [Finite η]
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {N : Set X0} {phi : C(H0, H0)}
    {j : η → V2 → X0} {theta : η → C0} {alpha beta a b : ℝ}
    (good : HamiltonZeroHomeomorphicDiskInstallation e d N phi j theta alpha beta a b)
    (hj : ∀ i, PolyhedralPLInCharts e (j i) Disk)
    (hrim : ∀ i (z : Disk), j i z ∈ frontier N ↔ (z : V2) ∈ Rim)
    (hdis : Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)))
    (xi : C0)
    (hcover : N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {xi} ⊆ ⋃ i, j i '' Disk)
    (hN : IsClosed N)
    (J : C(Ann, X0)) (hJi : Topology.IsEmbedding J)
    (hJN : range J ⊆ frontier N)
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c)
    (delta0 delta1 : ℝ) (tau : C0)
    (hformula : ∀ z : Ann, hamiltonZeroAmbientMap phi (J z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 tau (c z)) :
    delta0 ≠ delta1 := by
  intro hfold
  subst delta1
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : CompactSpace Ann := Dehn.annulusCylinderHomeomorph.compactSpace
  let : T2Space X0 :=
    (hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates).isEmbedding.t2Space
  have hcsurj : Function.Surjective c := by
    apply range_eq_univ.mp
    apply IsClopen.eq_univ
      ⟨(isCompact_range c.continuous).isClosed, hc.isOpenMap.isOpen_range⟩
    exact ⟨c (Dehn.annulusRimPoint false 0), mem_range_self _⟩
  obtain ⟨z, hz⟩ := hcsurj (0, xi)
  obtain ⟨n, arc, hi, _, hwhole, hcoord, _⟩ := hc.exists_finite_vertical_arc_family xi
  have hzmem : z ∈ ⋃ i, range (arc i) := by
    rw [hwhole]
    exact congrArg Prod.snd hz
  obtain ⟨i, _, _⟩ := mem_iUnion.mp hzmem
  let k : C(unitInterval, X0) := J.comp (arc i)
  have hkfront (t : unitInterval) : k t ∈ frontier N := hJN (mem_range_self _)
  have hkphase (t : unitInterval) : hamiltonZeroThirdCircleMap phi (k t) = xi := by
    rw [hamiltonZeroThirdCircleMap_ambient]
    change ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
      (hamiltonZeroAmbientMap phi (J (arc i t)))).1.1 = xi
    rw [hformula, hamiltonZeroAnnulusTargetMap_coordinates, hcoord]
  have hkconstant (t : unitInterval) :
      hamiltonZeroAmbientMap phi (k t) = hamiltonZeroAmbientMap phi (k 0) := by
    change hamiltonZeroAmbientMap phi (J (arc i t)) =
      hamiltonZeroAmbientMap phi (J (arc i 0))
    rw [hformula, hformula, hcoord, hcoord]
    simp only [hamiltonZeroAnnulusTargetMap, ContinuousMap.coe_mk,
      sub_self, zero_mul, zero_add]
  let M : η → Set X0 := fun i => j i '' Disk ∩ frontier N
  have hclosed (i : η) : IsClosed (M i) :=
    ((isCompact_closedBall (0 : V2) 1).image_of_continuousOn
      (hj i).continuousOn).isClosed.inter isClosed_frontier
  have hMdis : Pairwise (fun i k => Disjoint (M i) (M k)) :=
    fun i k hik => (hdis hik).mono inter_subset_left inter_subset_left
  have hkcover : range k ⊆ ⋃ i, M i := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hN.frontier_subset (hkfront t), hkphase t⟩)
    exact mem_iUnion.mpr ⟨i, hi, hkfront t⟩
  have heq := endpoints_eq_of_constant_in_finite_injective_cover M hclosed hMdis
    (hamiltonZeroAmbientMap phi) (good.injOn_disk_frontier hrim) k hkcover hkconstant
  exact zero_ne_one ((hJi.comp (hi i)).injective heq)

/-- For the two literal terminal disk families, completeness itself supplies
the selected fiber cover. Each normal-form annulus has the two distinct
retained-region endpoint labels, in one of their two orders. -/
theorem HamiltonZeroHomeomorphicDiskInstallation.opposite_labels_of_terminal_family
    {ι κ : Type*}
    {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {N : Set X0} {phi : C(H0, H0)}
    {n : Bool → ℕ} {j : (Σ s : Bool, Fin (n s)) → V2 → X0}
    {alpha beta a b u v : ℝ}
    (good : HamiltonZeroHomeomorphicDiskInstallation e d N phi j
      (fun i => ((if i.1 then v else u : ℝ) : C0)) alpha beta a b)
    (hj : ∀ i, PolyhedralPLInCharts e (j i) Disk)
    (hrim : ∀ i (z : Disk), j i z ∈ frontier N ↔ (z : V2) ∈ Rim)
    (hdis : Pairwise (fun i k => Disjoint (j i '' Disk) (j k '' Disk)))
    (hwhole : ∀ s : Bool, (⋃ i : Fin (n s), j ⟨s, i⟩ '' Disk) =
      N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {((if s then v else u : ℝ) : C0)})
    (hN : IsClosed N)
    (J : C(Ann, X0)) (hJi : Topology.IsEmbedding J)
    (hJN : range J ⊆ frontier N)
    (c : C(Ann, unitInterval × C0)) (hc : IsCoveringMap c)
    (delta0 delta1 : ℝ) (tau : C0)
    (hdelta0 : delta0 ∈ ({alpha, beta} : Set ℝ))
    (hdelta1 : delta1 ∈ ({alpha, beta} : Set ℝ))
    (hformula : ∀ z : Ann, hamiltonZeroAmbientMap phi (J z) =
      hamiltonZeroAnnulusTargetMap delta0 delta1 tau (c z)) :
    (delta0 = alpha ∧ delta1 = beta) ∨ (delta0 = beta ∧ delta1 = alpha) := by
  have hcover : N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(u : C0)} ⊆
      ⋃ i, j i '' Disk := by
    rw [← show (⋃ i : Fin (n false), j ⟨false, i⟩ '' Disk) =
      N ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(u : C0)} from hwhole false]
    exact iUnion_mono' (fun i => ⟨⟨false, i⟩, subset_rfl⟩)
  have hne := good.normal_labels_ne_of_annulus hj hrim hdis (u : C0) hcover
    hN J hJi hJN c hc delta0 delta1 tau hformula
  rcases hdelta0 with rfl | rfl <;> rcases hdelta1 with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (hne rfl).elim

end PoincareMT.M76

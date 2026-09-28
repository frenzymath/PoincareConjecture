import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.ClosedPhaseSphere
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.SecondCoordinateLifts
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
open Set Geometry
open scoped Topology

namespace PoincareConjecture.M76

theorem connectedComponentIn_eq_of_closed_piece
    {X : Type*} [TopologicalSpace X] {T F G S : Set X}
    [LocallyConnectedSpace T] (hF : IsClosed F) (hG : IsClosed G)
    (hT : T = F ∪ G) (hS : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S)
    (hdis : Disjoint S G) :
    ∀ x ∈ S, connectedComponentIn T x = S := by
  intro x hx
  have hFT : F ⊆ T := hT.symm ▸ subset_union_left
  have hST : S ⊆ T := hS.trans hFT
  have hSc : IsClosed S := by
    rw [← hcomponent x hx, connectedComponentIn_eq_image (hS hx)]
    exact hF.isClosedMap_subtype_val _ isClosed_connectedComponent
  let V : Set T := (Subtype.val : T → X) ⁻¹' Gᶜ
  have hV : IsOpen V := hG.isOpen_compl.preimage continuous_subtype_val
  have hSo : IsOpen ((Subtype.val : T → X) ⁻¹' S) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hyV : y ∈ V := fun hyG => disjoint_left.mp hdis hy hyG
    have hCC : connectedComponentIn V y ⊆ (Subtype.val : T → X) ⁻¹' S := by
      have hi : IsPreconnected
          ((Subtype.val : T → X) '' connectedComponentIn V y) :=
        isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
      have hsub := hi.subset_connectedComponentIn
        (mem_image_of_mem Subtype.val (mem_connectedComponentIn hyV)) (by
          rintro z ⟨w, hw, rfl⟩
          have hwG : (w : X) ∉ G := connectedComponentIn_subset V y hw
          exact (hT.subset w.property).resolve_right hwG)
      rw [hcomponent y hy] at hsub
      exact fun z hz => hsub (mem_image_of_mem _ hz)
    exact Filter.mem_of_superset
      ((hV.connectedComponentIn).mem_nhds (mem_connectedComponentIn hyV)) hCC
  have hclopen : IsClopen ((Subtype.val : T → X) ⁻¹' S) :=
    ⟨hSc.preimage continuous_subtype_val, hSo⟩
  apply Subset.antisymm
  · rw [connectedComponentIn_eq_image (hST hx)]
    rintro y ⟨z, hz, rfl⟩
    exact hclopen.connectedComponent_subset hx hz
  · rw [← hcomponent x hx]
    exact connectedComponentIn_mono x hFT

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_closed_marked_component_sphere
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    {N R F U S : Set X0} (he : PLDomain e N) (hN : IsCompact N)
    (hF : IsClosed F) (hU : IsClosed U)
    (hfront : frontier N = (N ∩ frontier R) ∪ (F ∪ U))
    (hFU : Disjoint F U) (hSne : S.Nonempty) (hS : S ⊆ F)
    (hcomponent : ∀ x ∈ S, connectedComponentIn F x = S)
    (hrim : Disjoint S (frontier R))
    (hcyclic : ∀ x : F, IsCyclic (FundamentalGroup F x)) :
    Nonempty (ChartwisePLSphere e S) := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hSF : S ⊆ frontier N := fun x hx => hfront.symm.subset (Or.inr (Or.inl (hS hx)))
  have hNne : N.Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    exact ⟨x, he.closed.frontier_subset (hSF hx)⟩
  obtain ⟨s, f, K, A, Hmodel, g, HB, _, _, _, _, hA, _⟩ :=
    he.exists_original_frontier_surface_model hN hNne
  let : LocallyPathConnectedSpace A.space := A.locallyPathConnectedSpace_of_finite hA
  let : LocallyPathConnectedSpace (frontier N) := HB.isQuotientMap.locallyPathConnectedSpace
  let G := (N ∩ frontier R) ∪ U
  have hG : IsClosed G := (he.closed.inter isClosed_frontier).union hU
  have hsplit : frontier N = F ∪ G := by
    rw [hfront]
    ext x
    simp only [G, mem_union]
    tauto
  have hdis : Disjoint S G := by
    apply disjoint_left.mpr
    intro x hx hxG
    rcases hxG with hxold | hxU
    · exact disjoint_left.mp hrim hx hxold.2
    · exact disjoint_left.mp hFU (hS hx) hxU
  have hwhole := connectedComponentIn_eq_of_closed_piece hF hG hsplit hS hcomponent hdis
  apply exists_hamiltonZero_whole_frontier_component_sphere e he hN hSne hSF hwhole
  intro x
  let : IsCyclic (FundamentalGroup F (ContinuousMap.inclusion hS x)) := hcyclic _
  exact isCyclic_of_injective (FundamentalGroup.map (ContinuousMap.inclusion hS) x)
    (FundamentalGroup.inclusion_injective_of_whole_component hS hcomponent x)

local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_closed_second_component_sphere
    {ι : Type*} (e : ι → OpenPartialHomeomorph X0 V3) (phi : C(H0, H0))
    {R S : Set X0} (hR : IsCompact R) {a b : ℝ} {theta theta' : C0}
    (he : PLDomain e (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p a b))
    (hfront : frontier (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p a b) =
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ∩
        frontier R) ∪
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}) ∪
        (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta'})))
    (hne : theta ≠ theta') (hSne : S.Nonempty)
    (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta})
    (hcomponent : ∀ x ∈ S,
      connectedComponentIn (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}) x = S)
    (hrim : Disjoint S (frontier R))
    (hcyclic : ∀ x : ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}),
      IsCyclic (FundamentalGroup ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {theta}) x)) :
    Nonempty (ChartwisePLSphere e S) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hN := hR.inter_right ((AddCircle.isCompact_closedIntervalArc p a b).isClosed.preimage
    (hamiltonZeroSecondCircleMap phi).continuous)
  have hclosed (t : C0) : IsClosed (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {t}) :=
    hR.isClosed.inter (isClosed_singleton.preimage (hamiltonZeroSecondCircleMap phi).continuous)
  apply exists_hamiltonZero_closed_marked_component_sphere e he hN
    (hclosed theta) (hclosed theta') hfront _ hSne hS hcomponent hrim hcyclic
  exact disjoint_left.mpr (fun x hx hy => hne (hx.2.symm.trans hy.2))

end PoincareConjecture.M76

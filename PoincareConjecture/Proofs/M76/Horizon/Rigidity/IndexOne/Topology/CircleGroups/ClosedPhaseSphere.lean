import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.OrientedFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.SourcePhase
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.ComponentGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.ClosedFrontier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Incidence.TwoRimModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Compression.Complement.Interior
import PoincareConjecture.Proofs.M76.Wall.OriginalFrontierSurfaceModel
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))



theorem exists_hamilton_whole_frontier_component_sphere
    {ι : Type*} (e : ι → OpenPartialHomeomorph X V3) {N S : Set X}
    (he : PLDomain e N) (hN : IsCompact N) (hSne : S.Nonempty)
    (hSF : S ⊆ frontier N)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (frontier N) x = S)
    (hcyclic : ∀ x : S, IsCyclic (FundamentalGroup S x)) :
    Nonempty (ChartwisePLSphere e S) := by
  classical
  let h := (Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))
  let : T2Space X := h.isEmbedding.t2Space
  obtain ⟨x, hx⟩ := hSne
  have hNne : N.Nonempty := ⟨x, he.closed.frontier_subset (hSF hx)⟩
  obtain ⟨s, F, K, A, Hmodel, g, HB, hFc, _, hK, hAK, hA, _, _, hAs,
    hH, _, hg, hgPL, _, _, hboundary, hstars, hpure, hcofaces, hlinks⟩ :=
    he.exists_original_frontier_surface_model hN hNne
  let q : (s → ℝ × V3) → X := fun z => g z
  have hqi : InjOn q K.space := by
    intro z hz w hw hzw
    have hh : Hmodel.symm ⟨z, hz⟩ = Hmodel.symm ⟨w, hw⟩ :=
      Subtype.ext ((hg ⟨z, hz⟩).symm.trans (hzw.trans (hg ⟨w, hw⟩)))
    exact congrArg Subtype.val (Hmodel.symm.injective hh)
  have hqF (y : X) (hy : y ∈ N) : q (F y) = y := by
    rw [← hH ⟨y, hy⟩]
    exact (hg (Hmodel ⟨y, hy⟩)).trans
      (congrArg Subtype.val (Hmodel.symm_apply_apply ⟨y, hy⟩))
  have hSconn : IsConnected S := by
    rw [← hcomponent x hx]
    exact isConnected_connectedComponentIn_iff.mpr (hSF hx)
  have hFA : F '' S ⊆ A.space := by
    rw [hAs]
    exact image_mono hSF
  obtain ⟨D, hD⟩ := A.exists_edgeComponentComplex_of_isConnected hA
    (hSconn.image F hFc.continuousOn) hFA
  let J := A.edgeComponentComplex D
  have hJA : J ≤ A := A.edgeComponentComplex_le D
  have hJK : J ≤ K := hJA.trans hAK
  have hJs : J.space ⊆ K.space := SimplicialComplex.space_subset_of_le hJK
  have hqfront : MapsTo q A.space (frontier N) := fun z hz =>
    (hboundary z (SimplicialComplex.space_subset_of_le hAK hz)).mpr hz
  have hxJ : F x ∈ J.space := hD (mem_image_of_mem F hx)
  have hqS : q '' J.space = S := by
    apply Subset.antisymm
    · rw [← hcomponent x hx]
      apply ((A.edgeComponentComplex_isPathConnected D).isConnected.image q
        (hgPL.continuousOn.mono hJs)).isPreconnected.subset_connectedComponentIn
      · exact ⟨F x, hxJ, hqF x (he.closed.frontier_subset (hSF hx))⟩
      · rintro _ ⟨z, hz, rfl⟩
        exact hqfront (SimplicialComplex.space_subset_of_le hJA hz)
    · intro y hy
      exact ⟨F y, hD (mem_image_of_mem F hy), hqF y (he.closed.frontier_subset (hSF hy))⟩
  have hJ : J.faces.Finite := hA.subset hJA
  let : CompactSpace J.space := isCompact_iff_compactSpace.mp
    (J.isCompact_space_of_finite hJ)
  let HC0 : J.space ≃ q '' J.space := Equiv.Set.imageOfInjOn q J.space (hqi.mono hJs)
  have hHC0 : Continuous HC0 := (hgPL.continuousOn.mono hJs).domRestrict.subtype_mk _
  let HC : J.space ≃ₜ S :=
    (HC0.toHomeomorphOfContinuousClosed hHC0 hHC0.isClosedMap).trans (Homeomorph.setCongr hqS)
  let z : J.space := ⟨F x, hxJ⟩
  let : IsCyclic (FundamentalGroup S (HC z)) := hcyclic (HC z)
  let : IsCyclic (FundamentalGroup J.space z) :=
    isCyclic_of_injective (FundamentalGroup.map ⟨HC, HC.continuous⟩ z)
      (FundamentalGroup.map_injective_of_leftInverse ⟨HC, HC.continuous⟩
        ⟨HC.symm, HC.symm.continuous⟩ HC.left_inv z)
  have hsphere := exists_hamilton_frontier_component_sphere_of_isCyclic e
    he.cover he.compatible K A hK hAK q N hgPL hqi hqfront
    (by intro p hp; convert! hstars p hp)
    hpure hcofaces (by intro p hp; convert! hlinks p hp) D z
  change Nonempty (ChartwisePLSphere e (q '' J.space)) at hsphere
  rw [hqS] at hsphere
  exact hsphere




theorem exists_closed_source_component_sphere
    {α β : Type*} (e : α → OpenPartialHomeomorph X V3)
    (d : β → OpenPartialHomeomorph X V3) (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    {u v : ℝ} {theta theta' : C}
    (heN : PLDomain e (sourceSlab phi u v))
    (hfront : frontier (sourceSlab phi u v) = (sourceSlab phi u v ∩ frontier R) ∪
      (sourceSurface phi theta ∪ sourceSurface phi theta'))
    (hAB : Disjoint (sourceSurface phi theta) (sourceSurface phi theta'))
    (hcorner : ∀ x ∈ sourceSurface phi theta ∩ frontier R,
      ∃ (psi lambda : V3 →ᴬ[ℝ] ℝ) (w z : V3) (G : OpenPartialHomeomorph X V3),
        psi.contLinear w = 1 ∧ psi.contLinear z = 0 ∧ lambda.contLinear z = 1 ∧
        x ∈ G.source ∧ psi (G x) = 0 ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ↔ 0 ≤ psi (G y)) ∧
        (∀ y ∈ G.source, y ∈ sourceSlab phi u v ∩ frontier R ↔
          psi (G y) = 0 ∧ 0 ≤ lambda (G y)) ∧
        ∀ y ∈ G.source, y ∈ sourceSurface phi theta ↔
          psi (G y) = 0 ∧ lambda (G y) ≤ 0)
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x))
    {S : Set X} (hSne : S.Nonempty) (hS : S ⊆ sourceSurface phi theta)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hrim : Disjoint S (frontier R)) :
    Nonempty (ChartwisePLSphere e S) := by
  let h := (Homeomorph.refl (Fin 1 → ℝ)).prodCongr
    (hamiltonLowerLatticePiEquiv (Fin 2))
  let : T2Space X := h.isEmbedding.t2Space
  obtain ⟨s, F, K, A, Hmodel, g, _, _, _, hK, _⟩ :=
    exists_compressed_sourceSurface_incidence_model e d phi hphi F0 heN hfront hAB hcorner
  have hSF : S ⊆ frontier (sourceSlab phi u v) := by
    intro x hx
    rw [hfront]
    exact Or.inr (Or.inl (hS hx))
  have hwhole := source_component_eq_frontier_component phi theta theta' K hK Hmodel
    heN.closed hfront hAB hS hcomponent hrim
  apply exists_hamilton_whole_frontier_component_sphere e heN (sourceSlab_isCompact phi u v)
    hSne hSF hwhole
  intro x
  let : IsCyclic (FundamentalGroup (sourceSurface phi theta) ((ContinuousMap.inclusion hS) x)) :=
    sourceSurface_pi1_isCyclic_of_ambient_injective phi theta F0 _ (hinj _)
  exact isCyclic_of_injective (FundamentalGroup.map (ContinuousMap.inclusion hS) x)
    (FundamentalGroup.inclusion_injective_of_whole_component hS hcomponent x)

end PoincareConjecture.M76.HamiltonIntervalTorus

import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimParametrization.FiniteModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimSubcomplexModel
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Collars.SourceCollarCoordinates



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "Q2" => sphere (0 : V2) 1



theorem exists_sourceRim_finitePL_circle_subcomplexes_of_injOn
    {α β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (F : X → E) (hFc : Continuous F)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (hFi : InjOn F (sourceSurface phi theta))
    (A : SimplicialComplex ℝ E) (hA : A.faces.Finite)
    (hAs : A.space = F '' (sourceSurface phi theta ∩ frontier R)) :
    ∃ J : Bool → SimplicialComplex ℝ E,
      (∀ side, J side ≤ A ∧ (J side).faces.Finite) ∧
      Pairwise (fun a b => Disjoint (J a).space (J b).space) ∧
      (⋃ side, (J side).space) = A.space ∧
      (∀ s, s ∈ A.faces ↔ ∃ side, s ∈ (J side).faces) ∧
      (∀ side, (J side).space = Set.range
        (fun z : sourceRimCircle phi theta F0 (originalIntervalEndpoint side) => F (z.val : X))) ∧
      ∃ (j : ∀ side, Q2 ≃ₜ sourceRimCircle phi theta F0 (originalIntervalEndpoint side))
        (gamma : ∀ side, Q2 ≃ₜ (J side).space),
        (∀ side, (gamma side).IsFinitePL ∧ (gamma side).symm.IsFinitePL) ∧
        ∀ side x, (gamma side x : E) = F ((j side x).val : X) := by
  classical
  let S := sourceSurface phi theta ∩ frontier R
  have hS : IsCompact S := (sourceSurface_isCompact phi theta).inter_right isClosed_frontier
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let f : S → A.space := fun x => ⟨F x, hAs.symm ▸ mem_image_of_mem F x.property⟩
  have hf : Continuous f := (hFc.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (hFi x.property.1 y.property.1 (congrArg Subtype.val h))
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hAs.subset y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let Hrim : S ≃ₜ A.space := hf.isClosedEmbedding hfi |>.isEmbedding.toHomeomorphOfSurjective hfs
  have hHrim (x : S) : (Hrim x : E) = F x := rfl
  obtain ⟨J, hJA, hdis, hcover, hfaces, delta, hdelta⟩ :=
    exists_sourceRim_circle_subcomplexes phi theta F0 A hA Hrim
  have hJs (side : Bool) : (J side).space = Set.range
      (fun z : sourceRimCircle phi theta F0 (originalIntervalEndpoint side) => F (z.val : X)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc⟩ := (delta side).surjective ⟨y, hy⟩
      refine ⟨sourceRimCircleCoordinates phi theta F0 (originalIntervalEndpoint side)
        (originalIntervalEndpoint_norm side) c, ?_⟩
      exact ((hdelta side c).trans (hHrim _)).symm.trans (congrArg Subtype.val hc)
    · rintro ⟨z, rfl⟩
      obtain ⟨c, rfl⟩ := (sourceRimCircleCoordinates phi theta F0
        (originalIntervalEndpoint side) (originalIntervalEndpoint_norm side)).surjective z
      have hv := (hdelta side c).trans (hHrim _)
      dsimp only
      rw [← hv]
      exact (delta side c).property
  have hg (side : Bool) :
      ∃ (j : Q2 ≃ₜ sourceRimCircle phi theta F0 (originalIntervalEndpoint side))
        (gamma : Q2 ≃ₜ (J side).space), gamma.IsFinitePL ∧ gamma.symm.IsFinitePL ∧
        ∀ x, (gamma x : E) = F ((j x).val : X) := by
    obtain ⟨j, gamma, hgamma, _, hval⟩ :=
      exists_sourceRimCircle_finitePL_parametrization hd phi hphi theta F0
        (originalIntervalEndpoint side) (originalIntervalEndpoint_norm side) F hF hFi
    let gamma' := gamma.trans (Homeomorph.setCongr (hJs side).symm)
    have hgamma' : gamma'.IsFinitePL := by
      obtain ⟨g, hg, hgv⟩ := hgamma
      exact ⟨g, hg, hgv⟩
    exact ⟨j, gamma', hgamma', hgamma'.symm, hval⟩
  choose j gamma hgamma hgammaInv hval using hg
  refine ⟨J, ?_, hdis, hcover, hfaces, hJs, j, gamma,
    fun side => ⟨hgamma side, hgammaInv side⟩, hval⟩
  intro side
  exact ⟨hJA side, hA.subset (hJA side)⟩



theorem exists_sourceRim_finitePL_circle_subcomplexes
    {α β E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {e : α → OpenPartialHomeomorph X V3}
    {d : β → OpenPartialHomeomorph X V3}
    (hd : StandardLatticeHandleAtlas (Fin 1) (Fin 2) L d)
    (phi : C(H, H))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 1) (Fin 2) L phi))
    (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (F : X → E) (hFc : Continuous F)
    (hF : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target)
    (N : Set X) (hRN : R ⊆ N)
    (K A : SimplicialComplex ℝ E) (hAK : A ≤ K) (hA : A.faces.Finite)
    (G : N ≃ₜ K.space) (hGF : ∀ x : N, (G x : E) = F x)
    (hAs : A.space = F '' (sourceSurface phi theta ∩ frontier R)) :
    ∃ J : Bool → SimplicialComplex ℝ E,
      (∀ side, J side ≤ A ∧ J side ≤ K ∧ (J side).faces.Finite) ∧
      Pairwise (fun a b => Disjoint (J a).space (J b).space) ∧
      (⋃ side, (J side).space) = A.space ∧
      (∀ s, s ∈ A.faces ↔ ∃ side, s ∈ (J side).faces) ∧
      (∀ side, (J side).space = Set.range
        (fun z : sourceRimCircle phi theta F0 (originalIntervalEndpoint side) => F (z.val : X))) ∧
      ∃ (j : ∀ side, Q2 ≃ₜ sourceRimCircle phi theta F0 (originalIntervalEndpoint side))
        (gamma : ∀ side, Q2 ≃ₜ (J side).space),
        (∀ side, (gamma side).IsFinitePL ∧ (gamma side).symm.IsFinitePL) ∧
        ∀ side x, (gamma side x : E) = F ((j side x).val : X) := by
  classical
  have hFiN : InjOn F N := by
    intro x hx y hy hxy
    have h : G ⟨x, hx⟩ = G ⟨y, hy⟩ := by
      apply Subtype.ext
      rw [hGF, hGF]
      exact hxy
    exact congrArg Subtype.val (G.injective h)
  have hFi : InjOn F (sourceSurface phi theta) :=
    hFiN.mono ((sourceSurface_subset phi theta).trans hRN)
  obtain ⟨J, hJA, hrest⟩ :=
    exists_sourceRim_finitePL_circle_subcomplexes_of_injOn
      hd phi hphi theta F0 F hFc hF hFi A hA hAs
  exact ⟨J, fun side => ⟨(hJA side).1, (hJA side).1.trans hAK, (hJA side).2⟩, hrest⟩

end PoincareConjecture.M76.HamiltonIntervalTorus

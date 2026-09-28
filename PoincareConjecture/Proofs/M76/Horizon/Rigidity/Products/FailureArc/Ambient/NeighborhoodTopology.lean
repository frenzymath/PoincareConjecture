import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Ambient.MetricNeighborhood
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonPLIrreducibility
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.NestedFiniteCoordinateCubes

set_option autoImplicit false
open Set Geometry Topology Metric

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem polyhedralPLInCharts_neighborhood_inclusion
    {X E ι : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : Set X} {e : ι → OpenPartialHomeomorph X V3}
    {d : ι × N → OpenPartialHomeomorph N V3}
    (hsource : ∀ k, MapsTo (Subtype.val : N → X) (d k).source (e k.1).source)
    (hval : ∀ k, (d k : N → V3) = (e k.1) ∘ Subtype.val)
    {f : E → N} {S : Set E} (hf : PolyhedralPLInCharts d f S) :
    PolyhedralPLInCharts e ((Subtype.val : N → X) ∘ f) S := by
  refine ⟨continuous_subtype_val.comp_continuousOn hf.continuousOn, ?_⟩
  intro x
  obtain ⟨k, K, U, hK, hKS, hU, hxU, hUK, hmaps, hcoords⟩ := hf.coordinates x
  refine ⟨k.1, K, U, hK, hKS, hU, hxU, hUK, (hsource k).comp hmaps, ?_⟩
  simpa only [hval, Function.comp_assoc] using hcoords


noncomputable def neighborhoodSubsetHomeomorph
    {X : Type*} [TopologicalSpace X] {N A : Set X} (hAN : A ⊆ N) :
    ((Subtype.val : N → X) ⁻¹' A) ≃ₜ A where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x, hAN x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem isPreconnected_neighborhood_preimage
    {X : Type*} [TopologicalSpace X] {N A : Set X}
    (hN : IsOpen N) (hAN : A ⊆ N) (hA : IsPreconnected A) :
    IsPreconnected ((Subtype.val : N → X) ⁻¹' A) :=
  hA.preimage_of_isOpenMap Subtype.val_injective hN.isOpenMap_subtype_val
    (by simpa only [Subtype.range_coe] using hAN)

theorem connectedComponentIn_neighborhood_preimage
    {X : Type*} [TopologicalSpace X] {N A : Set X}
    (hN : IsOpen N) (hAN : A ⊆ N) (x : N) (hx : (x : X) ∈ A) :
    connectedComponentIn ((Subtype.val : N → X) ⁻¹' A) x =
      (Subtype.val : N → X) ⁻¹' connectedComponentIn A (x : X) := by
  apply Subset.antisymm
  · have h := ((continuous_subtype_val : Continuous (Subtype.val : N → X)).continuousOn
      (s := (Subtype.val : N → X) ⁻¹' A)).image_connectedComponentIn_subset (a := x) hx
    have heq : (Subtype.val : N → X) '' ((Subtype.val : N → X) ⁻¹' A) = A :=
      image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hAN)
    rw [heq] at h
    exact fun y hy => h (mem_image_of_mem Subtype.val hy)
  · have hp := isPreconnected_neighborhood_preimage hN
      ((connectedComponentIn_subset A (x : X)).trans hAN)
      (isPreconnected_connectedComponentIn (x := (x : X)) (F := A))
    exact hp.subset_connectedComponentIn (mem_connectedComponentIn hx)
      (preimage_mono (connectedComponentIn_subset A (x : X)))


theorem whole_frontier_component_in_neighborhood
    {X : Type*} [TopologicalSpace X] {N R F : Set X}
    (hN : IsOpen N) (hRN : R ⊆ N) (hR : IsClosed R)
    (hfront : frontier ((Subtype.val : N → X) ⁻¹' R) =
      (Subtype.val : N → X) ⁻¹' frontier R)
    (x : F) (hF : F ⊆ frontier R)
    (hcomponent : connectedComponentIn (frontier R) (x : X) = F) :
    connectedComponentIn (frontier ((Subtype.val : N → X) ⁻¹' R))
      ⟨x, hRN (hR.frontier_subset (hF x.property))⟩ =
      (Subtype.val : N → X) ⁻¹' F := by
  rw [hfront, connectedComponentIn_neighborhood_preimage hN
    (hR.frontier_subset.trans hRN) _ (hF x.property), hcomponent]


theorem IsPLIrreducible.neighborhood_restriction
    {X : Type} {ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R N : Set X}
    (hI : IsPLIrreducible e R) (hRN : R ⊆ N)
    (d : ι × N → OpenPartialHomeomorph N V3)
    (hd : PLDomain d ((Subtype.val : N → X) ⁻¹' R))
    (hcenter : ∀ i x, x ∈ (d (i, x)).source ↔ (x : X) ∈ (e i).source)
    (hsource : ∀ k, MapsTo (Subtype.val : N → X) (d k).source (e k.1).source)
    (hval : ∀ k, (d k : N → V3) = (e k.1) ∘ Subtype.val)
    (hinterior : interior ((Subtype.val : N → X) ⁻¹' R) =
      (Subtype.val : N → X) ⁻¹' interior R) :
    IsPLIrreducible d ((Subtype.val : N → X) ⁻¹' R) := by
  classical
  refine ⟨hd, ?_⟩
  intro S hS hs
  obtain ⟨s⟩ := hs
  let H : S ≃ₜ ((Subtype.val : N → X) '' S) :=
    IsEmbedding.subtypeVal.homeomorphImage S
  let sph : ChartwisePLSphere e ((Subtype.val : N → X) '' S) :=
    { parametrization := s.parametrization.trans H
      map := Subtype.val ∘ s.map
      map_eq := fun z => congrArg Subtype.val (s.map_eq z)
      piecewiseAffine := polyhedralPLInCharts_neighborhood_inclusion hsource hval s.piecewiseAffine }
  have hSint : (Subtype.val : N → X) '' S ⊆ interior R := by
    rintro _ ⟨z, hz, rfl⟩
    exact hinterior.subset (hS hz)
  obtain ⟨D, hDR, b⟩ := hI.2 _ hSint ⟨sph⟩
  obtain ⟨b⟩ := b
  let B := (Subtype.val : N → X) ⁻¹' D
  let HB : B ≃ₜ D := neighborhoodSubsetHomeomorph (hDR.trans hRN)
  obtain ⟨K, hK, hKs⟩ := SimplicialComplex.exists_finite_coordinate_closedBall
    (0 : V3) (show (0 : ℝ) ≤ 1 by norm_num)
  let z₀ : K.space := ⟨0, hKs.symm ▸ mem_closedBall_self (show (0 : ℝ) ≤ 1 by norm_num)⟩
  have hbR : MapsTo b.map K.space R := by
    intro z hz
    rw [b.map_eq ⟨z, hKs.subset hz⟩]
    exact hDR (b.parametrization ⟨z, hKs.subset hz⟩).property
  let g (z : V3) : N := if hz : z ∈ K.space then ⟨b.map z, hRN (hbR hz)⟩
    else ⟨b.map z₀, hRN (hbR z₀.property)⟩
  have hgv : EqOn ((Subtype.val : N → X) ∘ g) b.map K.space := by
    intro z hz
    simp only [Function.comp_apply, g, dif_pos hz]
  have hgc : ContinuousOn g K.space := by
    apply IsEmbedding.subtypeVal.continuousOn_iff.mpr
    exact (hKs.symm ▸ b.piecewiseAffine.continuousOn).congr (fun z hz => hgv hz)
  have hg : PolyhedralPLInCharts d g K.space :=
    (hKs.symm ▸ b.piecewiseAffine).lift d (fun i x => (hcenter i x).mpr)
      (fun k x _ => congrFun (hval k) x) K hK hgc hgv
  refine ⟨B, preimage_mono hDR, ⟨{
    boundary_subset := ?_
    parametrization := b.parametrization.trans HB.symm
    map := g
    map_eq := ?_
    piecewiseAffine := hKs ▸ hg
    boundary_eq := ?_ }⟩⟩
  · intro z hz
    exact b.boundary_subset (mem_image_of_mem Subtype.val hz)
  · intro z
    apply Subtype.ext
    exact (hgv (hKs.symm.subset z.property)).trans (b.map_eq z)
  · intro z
    have hh := b.boundary_eq z
    change (b.parametrization z : X) ∈ (Subtype.val : N → X) '' S ↔ _ at hh
    have hmem : ((HB.symm (b.parametrization z) : B) : N) ∈ S ↔
        (b.parametrization z : X) ∈ (Subtype.val : N → X) '' S := by
      constructor
      · intro hz
        exact mem_image_of_mem Subtype.val hz
      · rintro ⟨y, hy, heq⟩
        have hyz : y = ((HB.symm (b.parametrization z) : B) : N) := Subtype.ext heq
        exact hyz ▸ hy
    exact hmem.trans hh

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.CompactDomain
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Transport.DomainProduct
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Transport.DiskRestriction
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Transport.Neighborhood
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Relative.Transport.ProductHomeomorph

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

attribute [local instance] Classical.propDecidable

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "K2" => Metric.closedBall (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "I+" => Icc (0 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  (e : ι → OpenPartialHomeomorph X V3) (D W O : Set X) (j : V2 → X)
  (K : Set X) (s : Finset (D ∪ K : Set X))

local notation "E" => (s → ℝ × V3)

structure RelativeFrontierDiskProduct where
  agreement : Set X
  compact_region : IsCompact K
  region_domain : PLDomain e K
  region_subset : K ⊆ W
  agreement_open : IsOpen agreement
  surface_in_agreement : frontier D ∩ W ⊆ agreement
  region_agreement : K ∩ agreement = W ∩ agreement
  frontier_agreement : ∀ x ∈ agreement, x ∈ frontier K ↔ x ∈ frontier W
  surface_agreement : frontier D ∩ K = frontier D ∩ W
  rim_agreement : frontier D ∩ frontier K = frontier D ∩ frontier W
  carrier : Set X
  compact_carrier : IsCompact carrier
  carrier_contains : D ∪ K ⊆ interior carrier
  stars : SimplicialComplex.CoorientedSurfaceStars E
  graph : X → E
  graph_continuous : Continuous graph
  graph_PL : ∀ i, LocallyPiecewiseAffineOn (graph ∘ (e i).symm) (e i).target
  model : carrier ≃ₜ stars.ambient.space
  model_eq : ∀ x : carrier, (model x : E) = graph x
  inverse : E → carrier
  inverse_eq : ∀ z : stars.ambient.space, (inverse z : X) = (model.symm z : X)
  inverse_PL : PolyhedralPLInCharts e (fun z ↦ (inverse z : X)) stars.ambient.space
  inverse_graph : ∀ x ∈ carrier, (inverse (graph x) : X) = x
  graph_inverse : ∀ z ∈ stars.ambient.space, graph (inverse z) = z
  ambient_image : stars.ambient.space = graph '' carrier
  region_image : (stars.marked 0).space = graph '' K
  boundary_image : (stars.marked 1).space = graph '' frontier K
  surface_image : (stars.marked 2).space = graph '' (frontier D ∩ W)
  rim_image : (stars.marked 3).space = graph '' (frontier D ∩ frontier W)
  product : E × ℝ → E
  product_PL : FinitePiecewiseAffineOn product ((stars.marked 2).space ×ˢ I)
  product_image : product '' ((stars.marked 2).space ×ˢ I) =
    ⋃ p : (stars.marked 2).vertices, stars.dualRegion {(p : E)}
  product_central : ∀ x ∈ (stars.marked 2).space, product (x, 0) = x
  product_region : ∀ z ∈ (stars.marked 2).space ×ˢ I, (inverse (product z) : X) ∈ K
  product_domain : ∀ z ∈ (stars.marked 2).space ×ˢ I,
    (inverse (product z) : X) ∈ D ↔ 0 ≤ z.2
  product_frontier : ∀ z ∈ (stars.marked 2).space ×ˢ I,
    (inverse (product z) : X) ∈ frontier D ↔ z.2 = 0
  product_boundary : ∀ z ∈ (stars.marked 2).space ×ˢ I,
    (inverse (product z) : X) ∈ frontier K ↔ (inverse z.1 : X) ∈ frontier K
  productHomeomorph : ((stars.marked 2).space ×ˢ I) ≃ₜ
    (⋃ p : (stars.marked 2).vertices, stars.dualRegion {(p : E)})
  productHomeomorph_PL : productHomeomorph.IsFinitePL
  productHomeomorph_inverse_PL : productHomeomorph.symm.IsFinitePL
  productHomeomorph_eq : ∀ z : ((stars.marked 2).space ×ˢ I),
    (productHomeomorph z : E) = product z
  productInverse : E → E × ℝ
  productInverse_PL : FinitePiecewiseAffineOn productInverse
    (⋃ p : (stars.marked 2).vertices, stars.dualRegion {(p : E)})
  productInverse_eq : ∀ z : (⋃ p : (stars.marked 2).vertices, stars.dualRegion {(p : E)}),
    (productHomeomorph.symm z : E × ℝ) = productInverse z
  productInverse_left : ∀ z ∈ (stars.marked 2).space ×ˢ I,
    productInverse (product z) = z
  productInverse_right : ∀ z ∈ (⋃ p : (stars.marked 2).vertices, stars.dualRegion {(p : E)}),
    product (productInverse z) = z
  neighborhood : Set X
  neighborhood_open : IsOpen neighborhood
  surface_in_neighborhood : frontier D ∩ W ⊆ neighborhood
  neighborhood_subset : neighborhood ⊆ interior carrier ∩ agreement
  neighborhood_coordinates : ∀ x ∈ neighborhood ∩ W,
    graph x ∈ (⋃ p : (stars.marked 2).vertices, stars.dualRegion {(p : E)})
  neighborhood_inverse : ∀ x ∈ neighborhood ∩ W,
    (inverse (product (productInverse (graph x))) : X) = x
  delta : ℝ
  delta_pos : 0 < delta
  delta_le : delta ≤ 1 / 2
  map : V2 × ℝ → X
  map_eq : ∀ z, map z = inverse (product (graph (j z.1), delta * z.2))
  map_PL : PolyhedralPLInCharts e map (K2 ×ˢ I+)
  map_injective : InjOn map (K2 ×ˢ I+)
  map_inside : MapsTo map (K2 ×ˢ I+) (D ∩ W ∩ O ∩ agreement)
  map_central : ∀ z ∈ K2, map (z, 0) = j z
  map_frontier : ∀ z ∈ K2 ×ˢ I+, map z ∈ frontier D ↔ z.2 = 0
  map_boundary : ∀ z ∈ K2 ×ˢ I+, map z ∈ frontier W ↔ j z.1 ∈ frontier W
  map_productInverse : ∀ z ∈ K2 ×ˢ I+,
    productInverse (graph (map z)) = (graph (j z.1), delta * z.2)

omit K s in

theorem exists_confined_relative_frontier_disk_collar_with_product
    [T2Space X]
    (hD : IsCompact D) (heD : PLDomain e D) (heW : PLDomain e W)
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B x = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
        ∀ y ∈ B.source, y ∈ frontier W ↔ B y 1 = 0)
    (hj : PolyhedralPLInCharts e j K2) (hji : InjOn j K2)
    (hjD : MapsTo j K2 (frontier D)) (hjW : MapsTo j K2 W)
    (hO : IsOpen O) (hjO : j '' K2 ⊆ O) :
    ∃ (K : Set X) (s : Finset (D ∪ K : Set X)),
      Nonempty (RelativeFrontierDiskProduct e D W O j K s) := by
  classical
  obtain ⟨K, V, hK, heK, hKW, hV, hSV, hKV, hfrontV, hsurface, hrim, hcrossK⟩ :=
    heW.exists_compact_relative_frontier_domain_with_agreement hD hcross
  have hjK : MapsTo j K2 K := fun z hz ↦ (hsurface.symm.subset ⟨hjD hz, hjW hz⟩).2
  have hne : (D ∪ K).Nonempty :=
    ⟨j 0, Or.inl (heD.closed.frontier_subset (hjD (by simp)))⟩
  obtain ⟨s, F, C, T, H, g, f, hC, hDC, hFc, hF, hKs, hM0, hM1, hM2, hM3,
    hHF, _, hg, hgPL, hgi, hleft, hright, hf, hfi, hfA, himage, hf0,
    hfK, hfD, hffD, hffK⟩ :=
    exists_signed_domain_surface_product hD heD hK heK hne hcrossK
  obtain ⟨HP, hHP, hHPinv, hHPval⟩ := T.exists_homeomorph_of_model_product hf hfi himage
  obtain ⟨r, hr, hrval⟩ := hHPinv
  have hrleft (z) (hz : z ∈ (T.marked 2).space ×ˢ I) : r (f z) = z := by
    rw [← hHPval ⟨z, hz⟩, ← hrval, HP.symm_apply_apply]
  have hrright (z) (hz : z ∈ ⋃ p : (T.marked 2).vertices,
      T.dualRegion {(p : s → ℝ × V3)}) : f (r z) = z := by
    rw [← hrval ⟨z, hz⟩, ← hHPval, HP.apply_symm_apply]
  obtain ⟨N, hN, hSN, hNC, _, hNinv⟩ := T.exists_realized_neighborhood_in_dual_union
    hFc H g (fun x hx ↦ hDC (Or.inr hx)) inter_subset_right hM0 hM2 hHF hg
  let N' := N ∩ V
  have hlocal (x : X) (hx : x ∈ N' ∩ W) :
      F x ∈ (⋃ p : (T.marked 2).vertices, T.dualRegion {(p : s → ℝ × V3)}) ∧
      (g (f (r (F x))) : X) = x := by
    have hxK : x ∈ K := (hKV.symm.subset ⟨hx.2, hx.1.2⟩).1
    have hc := hNinv x ⟨hx.1.1, hxK⟩
    exact ⟨hc.1, (congrArg (fun z ↦ (g z : X)) (hrright (F x) hc.1)).trans hc.2⟩
  have hjS : MapsTo (F ∘ j) K2 (T.marked 2).space :=
    fun z hz ↦ hM2.symm.subset ⟨j z, ⟨hjD hz, hjK hz⟩, rfl⟩
  have hgj : ∀ z ∈ K2, (g (F (j z)) : X) = j z := by
    intro z hz
    exact hleft (j z) (interior_subset (hDC (Or.inl (heD.closed.frontier_subset (hjD hz)))))
  have hjOV : j '' K2 ⊆ O ∩ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hjO ⟨z, hz, rfl⟩, hSV ⟨hjD hz, hjW hz⟩⟩
  obtain ⟨δ, k, hδ, hδsmall, hkval, hk, hki, hinside, hcenter, hfrontD, hfrontK⟩ :=
    exists_confined_disk_collar_of_finite_surface_product F (fun z ↦ (g z : X))
      hF hgPL hgi f hf hfi hfA hf0 hfK hfD hffD hffK j hj hji hjS hgj
      (hO.inter hV) hjOV
  refine ⟨K, s, ⟨{
    agreement := V
    compact_region := hK
    region_domain := heK
    region_subset := hKW
    agreement_open := hV
    surface_in_agreement := hSV
    region_agreement := hKV
    frontier_agreement := hfrontV
    surface_agreement := hsurface
    rim_agreement := hrim
    carrier := C
    compact_carrier := hC
    carrier_contains := hDC
    stars := T
    graph := F
    graph_continuous := hFc
    graph_PL := hF
    model := H
    model_eq := hHF
    inverse := g
    inverse_eq := hg
    inverse_PL := hgPL
    inverse_graph := hleft
    graph_inverse := hright
    ambient_image := hKs
    region_image := hM0
    boundary_image := hM1
    surface_image := hM2.trans (congrArg (fun A ↦ F '' A) hsurface)
    rim_image := hM3.trans (congrArg (fun A ↦ F '' A) hrim)
    product := f
    product_PL := hf
    product_image := himage
    product_central := hf0
    product_region := hfK
    product_domain := hfD
    product_frontier := hffD
    product_boundary := hffK
    productHomeomorph := HP
    productHomeomorph_PL := hHP
    productHomeomorph_inverse_PL := hHP.symm
    productHomeomorph_eq := hHPval
    productInverse := r
    productInverse_PL := hr
    productInverse_eq := hrval
    productInverse_left := hrleft
    productInverse_right := hrright
    neighborhood := N'
    neighborhood_open := hN.inter hV
    surface_in_neighborhood := fun x hx ↦ ⟨hSN (hsurface.symm.subset hx), hSV hx⟩
    neighborhood_subset := fun _ hx ↦ ⟨hNC hx.1, hx.2⟩
    neighborhood_coordinates := fun x hx ↦ (hlocal x hx).1
    neighborhood_inverse := fun x hx ↦ (hlocal x hx).2
    delta := δ
    delta_pos := hδ
    delta_le := hδsmall
    map := k
    map_eq := hkval
    map_PL := hk
    map_injective := hki
    map_inside := ?_
    map_central := hcenter
    map_frontier := hfrontD
    map_boundary := ?_
    map_productInverse := ?_ }⟩⟩
  · intro z hz
    exact ⟨⟨⟨(hinside hz).1.1, hKW (hinside hz).1.2⟩, (hinside hz).2.1⟩,
      (hinside hz).2.2⟩
  · intro z hz
    exact (hfrontV (k z) (hinside hz).2.2).symm.trans
      ((hfrontK z hz).trans (hfrontV (j z.1) (hSV ⟨hjD hz.1, hjW hz.1⟩)))
  · intro z hz
    have ht : δ * z.2 ∈ I := by
      constructor <;> nlinarith [hz.2.1, hz.2.2]
    have hparam : (F (j z.1), δ * z.2) ∈ (T.marked 2).space ×ˢ I := ⟨hjS hz.1, ht⟩
    rw [hkval, hright _ (hfA hparam)]
    exact hrleft _ hparam

end PoincareConjecture.M76

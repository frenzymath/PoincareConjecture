import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalOwnerIntersection
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem affine_mapsTo_of_convex_germ
    (G : V →ᴬ[ℝ] E) {S W : Set V} (hS : Convex ℝ S)
    {q : V} (hq : q ∈ S) (hW : IsOpen W) (hqW : q ∈ W)
    (C : AffineSubspace ℝ E) (hlocal : MapsTo G (S ∩ W) C) :
    MapsTo G S C := by
  intro x hx
  have hqC : G q ∈ C := hlocal ⟨hq, hqW⟩
  have hc : Continuous (fun r : ℝ ↦ AffineMap.lineMap q x r) := by
    simp only [AffineMap.lineMap_apply_module']
    fun_prop
  have hnear : ∀ᶠ r in 𝓝[>] (0 : ℝ), AffineMap.lineMap q x r ∈ W := by
    have h := hc.continuousAt.tendsto.eventually
      (show W ∈ 𝓝 (AffineMap.lineMap q x (0 : ℝ)) by simpa using hW.mem_nhds hqW)
    exact h.filter_mono nhdsWithin_le_nhds
  have hlt : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hrW, hrpos, hrlt⟩ := (hnear.and (hpos.and hlt)).exists
  have hrS : AffineMap.lineMap q x r ∈ S :=
    hS.segment_subset hq hx (lineMap_mem_segment ℝ q x ⟨hrpos.le, hrlt.le⟩)
  have hrC : AffineMap.lineMap (G q) (G x) r ∈ C := by
    have hG : G (AffineMap.lineMap q x r) = AffineMap.lineMap (G q) (G x) r :=
      G.toAffineMap.apply_lineMap q x r
    rw [← hG]
    exact hlocal ⟨hrS, hrW⟩
  have hext := AffineMap.lineMap_mem r⁻¹ hqC hrC
  simpa [AffineMap.lineMap_lineMap_right, ne_of_gt hrpos] using hext

theorem original_owner_eq_of_affine_germ [FiniteDimensional ℝ V]
    [DecidableEq V] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (L : SimplicialComplex ℝ V)
    {T U : Finset E} (hTf : T ∈ K.faces) (hUf : U ∈ K.faces)
    (hTc : T.card = 3) (hUc : U.card = 3)
    {t : Finset V} (ht : t ∈ L.faces) (htc : t.card = 3)
    (G : V →ᴬ[ℝ] E)
    (hi : InjOn G (convexHull ℝ (t : Set V)))
    (hT : MapsTo G (convexHull ℝ (t : Set V)) (convexHull ℝ (T : Set E)))
    {q : V} (hq : q ∈ convexHull ℝ (t : Set V))
    {W : Set V} (hW : IsOpen W) (hqW : q ∈ W)
    (hU : MapsTo G (convexHull ℝ (t : Set V) ∩ W) (convexHull ℝ (U : Set E))) :
    T = U := by
  have hlocal : MapsTo G (convexHull ℝ (t : Set V) ∩ W)
      (affineSpan ℝ ((T ∩ U : Finset E) : Set E)) := by
    intro x hx
    apply convexHull_subset_affineSpan
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hTf hUf]
    exact ⟨hT hx.1, hU hx⟩
  have hfull := affine_mapsTo_of_convex_germ G (convex_convexHull ℝ _) hq hW hqW
    (affineSpan ℝ ((T ∩ U : Finset E) : Set E)) hlocal
  have hind := G.toAffineMap.affineIndependent_comp_of_injOn_convexHull
    (p := ((↑) : t → V)) (L.indep ht) (by rwa [Subtype.range_coe])
  have himage : AffineIndependent ℝ ((↑) : (t.image G) → E) := by
    have hr : range (G.toAffineMap ∘ ((↑) : t → V)) = (t.image G : Set E) := by
      rw [Finset.coe_image, range_comp, Subtype.range_coe]
      rfl
    have h := hind.range
    change AffineIndependent ℝ ((↑) : range (G.toAffineMap ∘ ((↑) : t → V)) → E) at h
    rwa [hr] at h
  have hsubset : (t.image G : Set E) ⊆ affineSpan ℝ ((T ∩ U : Finset E) : Set E) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hfull (subset_convexHull ℝ _ hx)
  have hcard := himage.card_le_card_of_subset_affineSpan hsubset
  have himagecard : (t.image G).card = t.card :=
    Finset.card_image_of_injOn (hi.mono (subset_convexHull ℝ _))
  rw [himagecard, htc] at hcard
  have hinter : T ∩ U = T :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  exact Finset.eq_of_subset_of_card_le
    (hinter ▸ Finset.inter_subset_right) (by omega)

theorem original_owner_eq_of_affineOnFaces_germ [FiniteDimensional ℝ V]
    [DecidableEq V] [DecidableEq E]
    (K : SimplicialComplex ℝ E) (L : SimplicialComplex ℝ V)
    {T U : Finset E} (hTf : T ∈ K.faces) (hUf : U ∈ K.faces)
    (hTc : T.card = 3) (hUc : U.card = 3)
    {t : Finset V} (ht : t ∈ L.faces) (htc : t.card = 3)
    (F : V → E) (hF : L.AffineOnFaces F)
    (hi : InjOn F (convexHull ℝ (t : Set V)))
    (hT : MapsTo F (convexHull ℝ (t : Set V)) (convexHull ℝ (T : Set E)))
    {q : V} (hq : q ∈ convexHull ℝ (t : Set V))
    {W : Set V} (hW : IsOpen W) (hqW : q ∈ W)
    (hU : MapsTo F (convexHull ℝ (t : Set V) ∩ W) (convexHull ℝ (U : Set E))) :
    T = U := by
  obtain ⟨G, hG⟩ := hF t ht
  apply original_owner_eq_of_affine_germ K L hTf hUf hTc hUc ht htc G
  · intro x hx y hy hxy
    exact hi hx hy ((hG hx).trans (hxy.trans (hG hy).symm))
  · intro x hx
    rw [← hG hx]
    exact hT hx
  · exact hq
  · exact hW
  · exact hqW
  · intro x hx
    rw [← hG hx.1]
    exact hU hx

end PoincareConjecture.M76.OriginalTriangleCopies

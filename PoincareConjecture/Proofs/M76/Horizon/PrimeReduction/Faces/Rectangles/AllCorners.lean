import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.CornerComponentTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.NextCornerRectangle









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

theorem exists_next_original_corner_rectangle
    {ι : Type*} [Finite ι] (D : ι → Set (ℝ × ℝ)) (p q : ι → ℝ × ℝ)
    (hD : ∀ k, IsFinitePLBallPair ℝ (D k) {p k, q k})
    (hsub : ∀ k, D k ⊆ base)
    (hrim : ∀ k, ({p k, q k} : Set (ℝ × ℝ)) = D k ∩ frontier base)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hleft : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0})
    (hdiagonal : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {x ∈ base | x.1 + x.2 = 1})
    (c : Fin 3) (i : ι) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hi : cornerMap c '' ({p i, q i} : Set (ℝ × ℝ)) = {(0, b), (a, 0)})
    (hnext : ∃ k, ∃ u ∈ Ioo (0 : ℝ) 1, ∃ v ∈ Ioo (0 : ℝ) 1,
      cornerMap c '' ({p k, q k} : Set (ℝ × ℝ)) = {(0, v), (u, 0)} ∧ a < u) :
    ∃ j, ∃ u ∈ Ioo (0 : ℝ) 1, ∃ v ∈ Ioo (0 : ℝ) 1,
      i ≠ j ∧ cornerMap c '' ({p j, q j} : Set (ℝ × ℝ)) = {(0, v), (u, 0)} ∧ a < u ∧
      ∃ M : Set (ℝ × ℝ),
        IsFinitePLBallPair (ℝ × ℝ) M (D i ∪ (D j ∪ cornerMap c '' edgeIntervals a b u v)) ∧
        M ∩ frontier base = cornerMap c '' edgeIntervals a b u v ∧
        (∀ k, k ≠ i → k ≠ j → Disjoint (D k) M) ∧
        (∀ x ∈ M \ (D i ∪ D j),
          connectedComponentIn (base \ ⋃ k, D k) x = M \ (D i ∪ D j) ∧
          closure (connectedComponentIn (base \ ⋃ k, D k) x) = M) ∧
        ∃ G : (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) ≃ₜ M,
          G.IsFinitePL ∧
          (∀ x, (G x : ℝ × ℝ) ∈ D i ↔ (x : ℝ × ℝ).2 = 0) ∧
          (∀ x, (G x : ℝ × ℝ) ∈ D j ↔ (x : ℝ × ℝ).2 = 1) ∧
          (∀ x, (G x : ℝ × ℝ) ∈ cornerMap c '' ({0} ×ˢ Icc b v) ↔ (x : ℝ × ℝ).1 = 0) ∧
          (∀ x, (G x : ℝ × ℝ) ∈ cornerMap c '' (Icc a u ×ˢ {0}) ↔ (x : ℝ × ℝ).1 = 1) := by
  obtain ⟨hD', hsub', hrim', hdis', hleft', hbottom'⟩ :=
    normal_family_in_corner_coordinates c D p q hD hsub hrim hdis hleft hbottom hdiagonal
  obtain ⟨j, u, hu, v, hv, hne, hj, hau, M, hM, hMB, hother, hcomponent,
      C, hC, hCW, hCZ, hCL, hCR⟩ := exists_next_corner_component_rectangle
        (fun k => cornerMap c '' D k) (fun k => cornerMap c (p k)) (fun k => cornerMap c (q k))
        hD' hsub' hrim' hdis' hleft' hbottom' i ha hb
        (by simpa only [image_insert_eq, image_singleton] using hi)
        (by simpa only [image_insert_eq, image_singleton] using hnext)
  obtain ⟨G, hG, hGval⟩ := exists_corner_image_square_chart c C hC
  have hM' := hM.affine_image (cornerMap c) (cornerMap_involutive c).injective.injOn
  simp only [image_union, cornerMap_image_image] at hM'
  refine ⟨j, u, hu, v, hv, hne, by simpa only [image_insert_eq, image_singleton] using hj,
    hau, cornerMap c '' M, hM', ?_, ?_, ?_, G, hG, ?_, ?_, ?_, ?_⟩
  · rw [← hMB]
    ext x
    simp only [mem_inter_iff, mem_cornerMap_image, cornerMap_mem_frontier]
  · intro k hki hkj
    apply disjoint_left.mpr
    intro x hxD hxM
    exact disjoint_left.mp (hother k hki hkj) (mem_image_of_mem (cornerMap c) hxD)
      ((mem_cornerMap_image c M x).mp hxM)
  · intro x hx
    have hxM : cornerMap c x ∈ M := (mem_cornerMap_image c M x).mp hx.1
    have hxcoord : cornerMap c x ∈ M \ ((cornerMap c '' D i) ∪ (cornerMap c '' D j)) := by
      refine ⟨hxM, ?_⟩
      simp only [mem_union, mem_cornerMap_image, cornerMap_involutive c x]
      exact hx.2
    have he := (hcomponent (cornerMap c x) hxcoord).1
    have hxsource : cornerMap c x ∈ base \ ⋃ k, cornerMap c '' D k :=
      connectedComponentIn_subset _ _ (he.symm.subset hxcoord)
    have himage := cornerMap_image_arc_component c D hxsource
    rw [he, cornerMap_involutive, cornerMap_image_difference, image_union,
      cornerMap_image_image, cornerMap_image_image] at himage
    refine ⟨himage.symm, ?_⟩
    have hcl := (cornerHomeomorph c).image_closure
      (connectedComponentIn (base \ ⋃ k, cornerMap c '' D k) (cornerMap c x))
    change cornerMap c '' closure (connectedComponentIn (base \ ⋃ k, cornerMap c '' D k)
      (cornerMap c x)) = closure (cornerMap c '' connectedComponentIn
        (base \ ⋃ k, cornerMap c '' D k) (cornerMap c x)) at hcl
    rw [(hcomponent (cornerMap c x) hxcoord).2,
      cornerMap_image_arc_component c D hxsource, cornerMap_involutive] at hcl
    exact hcl.symm
  · intro x
    rw [hGval]
    exact (mem_cornerMap_image c (D i) (C x)).symm.trans (hCW x)
  · intro x
    rw [hGval]
    exact (mem_cornerMap_image c (D j) (C x)).symm.trans (hCZ x)
  · intro x
    rw [hGval, mem_cornerMap_image, cornerMap_involutive]
    exact hCL x
  · intro x
    rw [hGval, mem_cornerMap_image, cornerMap_involutive]
    exact hCR x

end PoincareConjecture.M76.TriangleCorner

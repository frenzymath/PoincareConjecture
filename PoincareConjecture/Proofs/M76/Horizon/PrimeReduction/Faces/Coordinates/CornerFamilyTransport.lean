import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.NormalCornerTypes









set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

theorem no_return_in_corner_coordinates (c : Fin 3) {r : Set (ℝ × ℝ)}
    (hr : r ⊆ base)
    (hleft : ¬ r ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ¬ r ⊆ Icc (0 : ℝ) 1 ×ˢ {0})
    (hdiagonal : ¬ r ⊆ {x ∈ base | x.1 + x.2 = 1}) :
    (¬ cornerMap c '' r ⊆ {0} ×ˢ Icc (0 : ℝ) 1) ∧
      (¬ cornerMap c '' r ⊆ Icc (0 : ℝ) 1 ×ˢ {0}) := by
  have hb (x : ℝ × ℝ) (hx : x ∈ r) :
      x.1 ∈ Icc (0 : ℝ) 1 ∧ x.2 ∈ Icc (0 : ℝ) 1 := by
    have h := hr hx
    rw [base_eq_triangle, TriangleDiskModel.mem_right_region_iff] at h
    exact ⟨⟨h.1, by linarith [h.2.1, h.2.2]⟩, h.2.1, by linarith [h.1, h.2.2]⟩
  fin_cases c
  · constructor
    · intro h
      exact hleft (fun x hx => h ⟨x, hx, rfl⟩)
    · intro h
      exact hbottom (fun x hx => h ⟨x, hx, rfl⟩)
  · constructor
    · intro hbad
      apply hdiagonal
      intro x hx
      have h := hbad (mem_image_of_mem (cornerMap 1) hx)
      change (1 - x.1 - x.2 = 0 ∧ _) at h
      exact ⟨hr hx, by linarith [h.1]⟩
    · intro hbad
      apply hbottom
      intro x hx
      have h := hbad (mem_image_of_mem (cornerMap 1) hx)
      exact ⟨(hb x hx).1, h.2⟩
  · constructor
    · intro hbad
      apply hleft
      intro x hx
      have h := hbad (mem_image_of_mem (cornerMap 2) hx)
      exact ⟨h.1, (hb x hx).2⟩
    · intro hbad
      apply hdiagonal
      intro x hx
      have h := hbad (mem_image_of_mem (cornerMap 2) hx)
      change (_ ∧ 1 - x.1 - x.2 = 0) at h
      exact ⟨hr hx, by linarith [h.2]⟩




theorem normal_family_in_corner_coordinates
    {ι : Type*} (c : Fin 3) (D : ι → Set (ℝ × ℝ)) (p q : ι → ℝ × ℝ)
    (hD : ∀ k, IsFinitePLBallPair ℝ (D k) {p k, q k})
    (hsub : ∀ k, D k ⊆ base)
    (hrim : ∀ k, ({p k, q k} : Set (ℝ × ℝ)) = D k ∩ frontier base)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hleft : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1)
    (hbottom : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0})
    (hdiagonal : ∀ k, ¬ ({p k, q k} : Set (ℝ × ℝ)) ⊆ {x ∈ base | x.1 + x.2 = 1}) :
    (∀ k, IsFinitePLBallPair ℝ (cornerMap c '' D k) {cornerMap c (p k), cornerMap c (q k)}) ∧
      (∀ k, cornerMap c '' D k ⊆ base) ∧
      (∀ k, ({cornerMap c (p k), cornerMap c (q k)} : Set (ℝ × ℝ)) =
        (cornerMap c '' D k) ∩ frontier base) ∧
      Pairwise (fun i j => Disjoint (cornerMap c '' D i) (cornerMap c '' D j)) ∧
      (∀ k, ¬ ({cornerMap c (p k), cornerMap c (q k)} : Set (ℝ × ℝ)) ⊆
        {0} ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ k, ¬ ({cornerMap c (p k), cornerMap c (q k)} : Set (ℝ × ℝ)) ⊆
        Icc (0 : ℝ) 1 ×ˢ {0}) := by
  have hinj := (cornerMap_involutive c).injective
  have hnr (k : ι) := no_return_in_corner_coordinates c
    ((hD k).1.trans (hsub k)) (hleft k) (hbottom k) (hdiagonal k)
  simp only [image_insert_eq, image_singleton] at hnr
  refine ⟨?_, ?_, ?_, ?_, fun k => (hnr k).1, fun k => (hnr k).2⟩
  · intro k
    simpa only [image_insert_eq, image_singleton] using (hD k).affine_image (cornerMap c) hinj.injOn
  · intro k x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (cornerMap_mem_base c y).mpr (hsub k hy)
  · intro k
    have hpairs : cornerMap c '' ({p k, q k} : Set (ℝ × ℝ)) =
        {cornerMap c (p k), cornerMap c (q k)} := by simp only [image_insert_eq, image_singleton]
    rw [← hpairs, hrim k]
    ext x
    constructor
    · rintro ⟨y, ⟨hyD, hyB⟩, rfl⟩
      exact ⟨mem_image_of_mem _ hyD, (cornerMap_mem_frontier c y).mpr hyB⟩
    · rintro ⟨⟨y, hy, rfl⟩, hxB⟩
      exact ⟨y, ⟨hy, (cornerMap_mem_frontier c y).mp hxB⟩, rfl⟩
  · intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    exact disjoint_left.mp (hdis hij) hy ((hinj (hyx.trans hzx.symm)).symm ▸ hz)

end PoincareConjecture.M76.TriangleCorner

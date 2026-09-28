import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.SurfaceCollar.MovedDiskCoordinates









set_option autoImplicit false
open Set Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_original_moved_disk_annulus
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (hcover : ∀ y, ∃ i, y ∈ (e i).source)
    {D r : Set P2} (hD : IsFinitePLBallPair P2 D r)
    {f : P2 → X} (hf : PolyhedralPLInCharts e f D) (hfi : InjOn f D)
    (H : X ≃ₜ X)
    (hH : ∀ i j, (e i).symm.trans (H.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hnest : H '' (f '' D) ⊆ (f '' D) \ (f '' r)) :
    ∃ a : P2 → X,
      PolyhedralPLInCharts e a Ann ∧ InjOn a Ann ∧
      a '' Ann = (f '' D) \ (H '' (f '' (D \ r))) ∧
      (∀ x ∈ Ann, a x ∈ f '' r ↔ depth 8 x = -1) ∧
      (∀ x ∈ Ann, a x ∈ H '' (f '' r) ↔ depth 8 x = 1) := by
  obtain ⟨q,_,hqi,hqval,hqD,hqpair,hqimage,hqrimage⟩ :=
    exists_moved_disk_coordinates he hcover hD hf hfi H hH hnest
  let I := q '' D
  have hID : I ⊆ D := hqD.trans interior_subset
  have hqfront : frontier I = q '' r := hqpair.frontier_eq_of_finrank_eq rfl
  have hIball : IsFinitePLBallPair P2 I (frontier I) := hqfront.symm ▸ hqpair
  have hDball : IsFinitePLBallPair P2 D (frontier D) :=
    (hD.frontier_eq_of_finrank_eq rfl).symm ▸ hD
  obtain ⟨B,hB,hBo,hBi⟩ := Dehn.exists_square_annulus_nested_disks hIball hDball hqD
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (2 : ℝ)*1 < 8)
  obtain ⟨k,hk,hkv⟩ := hB
  have hkN (x : P2) (hx : x ∈ Ann) : k x ∈ D \ interior I := by
    rw [←hkv ⟨x,hx⟩]
    exact (B ⟨x,hx⟩).property
  have hki : InjOn k Ann := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (B.injective (Subtype.ext
      ((hkv ⟨x,hx⟩).trans (hxy.trans (hkv ⟨y,hy⟩).symm))))
  have hkimage : k '' Ann = D \ interior I := by
    apply Subset.antisymm (image_subset_iff.mpr hkN)
    intro x hx
    refine ⟨B.symm ⟨x,hx⟩,(B.symm ⟨x,hx⟩).property,?_⟩
    rw [←hkv,B.apply_symm_apply]
  obtain ⟨J,hJ,hJs,hkAff⟩ := hk
  have hkPL : FinitePiecewiseAffineOn k J.space := ⟨J,hJ,rfl,hkAff⟩
  have hfk : PolyhedralPLInCharts e (f ∘ k) Ann := hJs ▸
    hf.comp_finitePiecewiseAffineOn J hJ hkPL (fun x hx => (hkN x (hJs.subset hx)).1)
  have hinterior : f '' interior I = H '' (f '' (D \ r)) := by
    rw [hqpair.interior_eq_sdiff_of_finrank_eq rfl,←hqi.image_sdiff_subset hD.1,
      image_image,image_image]
    exact image_congr (fun x hx => hqval x hx.1)
  have hmem (z : P2) (hz : z ∈ D) {T : Set P2} (hTD : T ⊆ D) :
      f z ∈ f '' T ↔ z ∈ T := by
    constructor
    · rintro ⟨x,hx,hxz⟩
      exact hfi (hTD hx) hz hxz ▸ hx
    · exact fun h => mem_image_of_mem _ h
  refine ⟨f ∘ k,hfk,hfi.comp hki (fun x hx => (hkN x hx).1),?_,?_,?_⟩
  · calc
      (f ∘ k) '' Ann = f '' (k '' Ann) := (image_image f k Ann).symm
      _ = (f '' D) \ (H '' (f '' (D \ r))) := by
        rw [hkimage,hfi.image_sdiff_subset (interior_subset.trans hID),hinterior]
  · intro x hx
    have hmark := hBo ⟨x,hx⟩
    rw [hkv,hD.frontier_eq_of_finrank_eq rfl] at hmark
    exact (hmem (k x) (hkN x hx).1 hD.1).trans hmark.symm
  · intro x hx
    have hmark := hBi ⟨x,hx⟩
    rw [hkv,hqfront] at hmark
    rw [←hqrimage]
    exact (hmem (k x) (hkN x hx).1 ((image_mono hD.1).trans hID)).trans hmark.symm

end PoincareConjecture.M76

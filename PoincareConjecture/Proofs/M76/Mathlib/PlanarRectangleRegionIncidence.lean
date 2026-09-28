import PoincareConjecture.Proofs.M76.Mathlib.LocalRegionSideIncidence
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateHalfBoxes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInterior

set_option autoImplicit false

open Set Geometry CoordinateHalfBoxes

namespace Geometry

theorem inter_image_rectangle_eq_half_of_open_image
    {f : (ℝ × ℝ) → (ℝ × ℝ)} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (base r))
    (hopen : IsOpen (f '' (Ioo (-r) r ×ˢ Ioo (-r) r)))
    {D : Set (ℝ × ℝ)} (hD : IsClosed D) (hreg : closure (interior D) = D)
    (hfront : ∀ x ∈ base r, f x ∈ frontier D ↔ x.2 = 0) :
    D ∩ (f '' base r) = f '' (Icc (-r) r ×ˢ Icc (-r) 0) ∨
      D ∩ (f '' base r) = f '' (Icc (-r) r ×ˢ Icc 0 r) := by
  let U₀ : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) r
  let L₀ : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) 0
  let R₀ : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo 0 r
  let LC : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Icc (-r) 0
  let RC : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Icc 0 r
  have hLC : LC ⊆ base r := fun _ hx => ⟨hx.1, hx.2.1, hx.2.2.trans hr.le⟩
  have hRC : RC ⊆ base r :=
    fun _ hx => ⟨hx.1, (neg_nonpos.mpr hr.le).trans hx.2.1, hx.2.2⟩
  have hU₀ : U₀ ⊆ base r := fun _ hx => ⟨⟨hx.1.1.le, hx.1.2.le⟩,
    hx.2.1.le, hx.2.2.le⟩
  have hL₀ : L₀ ⊆ LC := fun _ hx => ⟨⟨hx.1.1.le, hx.1.2.le⟩,
    hx.2.1.le, hx.2.2.le⟩
  have hR₀ : R₀ ⊆ RC := fun _ hx => ⟨⟨hx.1.1.le, hx.1.2.le⟩,
    hx.2.1.le, hx.2.2.le⟩
  have hclL₀ : closure L₀ = LC := by
    exact (closure_prod_eq).trans (by rw [closure_Ioo (by linarith : -r ≠ r),
      closure_Ioo (neg_ne_zero.mpr hr.ne')])
  have hclR₀ : closure R₀ = RC := by
    exact (closure_prod_eq).trans (by rw [closure_Ioo (by linarith : -r ≠ r),
      closure_Ioo hr.ne])
  have hclosedL : IsClosed (f '' LC) :=
    ((isCompact_Icc.prod isCompact_Icc).image_of_continuousOn (hf.mono hLC)).isClosed
  have hclosedR : IsClosed (f '' RC) :=
    ((isCompact_Icc.prod isCompact_Icc).image_of_continuousOn (hf.mono hRC)).isClosed
  have hclL : closure (f '' L₀) = f '' LC := by
    apply Subset.antisymm (closure_minimal (image_mono hL₀) hclosedL)
    rw [← hclL₀]
    exact (hf.mono (hclL₀.subset.trans hLC)).image_closure
  have hclR : closure (f '' R₀) = f '' RC := by
    apply Subset.antisymm (closure_minimal (image_mono hR₀) hclosedR)
    rw [← hclR₀]
    exact (hf.mono (hclR₀.subset.trans hRC)).image_closure
  have hL : IsPreconnected (f '' L₀) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image f (hf.mono (hL₀.trans hLC))
  have hR : IsPreconnected (f '' R₀) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image f (hf.mono (hR₀.trans hRC))
  have hcover : (f '' U₀) \ frontier D = (f '' L₀) ∪ (f '' R₀) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxD⟩
      have hx0 : x.2 ≠ 0 := fun h => hxD ((hfront x (hU₀ hx)).mpr h)
      rcases lt_or_gt_of_ne hx0 with hn | hp
      · exact Or.inl ⟨x, ⟨hx.1, hx.2.1, hn⟩, rfl⟩
      · exact Or.inr ⟨x, ⟨hx.1, hp, hx.2.2⟩, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · refine ⟨⟨x, ⟨hx.1, hx.2.1, hx.2.2.trans hr⟩, rfl⟩, ?_⟩
        exact fun h => hx.2.2.ne ((hfront x (hLC (hL₀ hx))).mp h)
      · refine ⟨⟨x, ⟨hx.1, (neg_lt_zero.mpr hr).trans hx.2.1, hx.2.2⟩, rfl⟩, ?_⟩
        exact fun h => hx.2.1.ne' ((hfront x (hRC (hR₀ hx))).mp h)
  have hzeroU : (0 : ℝ × ℝ) ∈ U₀ := by
    exact ⟨⟨neg_lt_zero.mpr hr, hr⟩, neg_lt_zero.mpr hr, hr⟩
  have hzeroD : f 0 ∈ frontier D := (hfront 0 (hU₀ hzeroU)).mpr rfl
  have hunion : LC ∪ RC = base r := by
    change (Icc (-r) r ×ˢ Icc (-r) 0) ∪ (Icc (-r) r ×ˢ Icc 0 r) = base r
    rw [← prod_union, Icc_union_Icc_eq_Icc (neg_nonpos.mpr hr.le) hr.le]
    rfl
  have himage : closure (f '' L₀) ∪ closure (f '' R₀) = f '' base r := by
    rw [hclL, hclR, ← image_union, hunion]
  have hRL : closure (f '' R₀) ∩ frontier D ⊆ closure (f '' L₀) := by
    rw [hclR, hclL]
    rintro y ⟨⟨x, hx, rfl⟩, hxD⟩
    have hx0 := (hfront x (hRC hx)).mp hxD
    refine ⟨x, ⟨hx.1, ?_, hx0.le⟩, rfl⟩
    simpa only [hx0] using neg_nonpos.mpr hr.le
  have hLR : closure (f '' L₀) ∩ frontier D ⊆ closure (f '' R₀) := by
    rw [hclL, hclR]
    rintro y ⟨⟨x, hx, rfl⟩, hxD⟩
    have hx0 := (hfront x (hLC hx)).mp hxD
    refine ⟨x, ⟨hx.1, hx0.ge, ?_⟩, rfl⟩
    simpa only [hx0] using hr.le
  rcases hD.local_complementary_sides hreg hzeroD hopen
      (mem_image_of_mem f hzeroU) hL hR hcover with h | h
  · have hresult := hD.inter_union_closure_eq_of_sides h.1 h.2 hRL
    rw [himage, hclL] at hresult
    exact Or.inl hresult
  · have hresult := hD.inter_union_closure_eq_of_sides h.1 h.2 hLR
    rw [union_comm (closure (f '' R₀)), himage, hclR] at hresult
    exact Or.inr hresult

theorem FinitePiecewiseAffineOn.inter_image_rectangle_eq_half
    {f : (ℝ × ℝ) → (ℝ × ℝ)} {r : ℝ} (hr : 0 < r)
    (hf : FinitePiecewiseAffineOn f (base r)) (hinj : InjOn f (base r))
    {D : Set (ℝ × ℝ)} (hD : IsClosed D) (hreg : closure (interior D) = D)
    (hfront : ∀ x ∈ base r, f x ∈ frontier D ↔ x.2 = 0) :
    D ∩ (f '' base r) = f '' (Icc (-r) r ×ˢ Icc (-r) 0) ∨
      D ∩ (f '' base r) = f '' (Icc (-r) r ×ˢ Icc 0 r) := by
  obtain ⟨e, he, hef⟩ := hf.exists_homeomorph_image hinj
  have hint : interior (base r) = Ioo (-r) r ×ˢ Ioo (-r) r := by
    rw [base, interior_prod_eq, interior_Icc]
  have himage : f '' interior (base r) = interior (f '' base r) := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact hf.mem_interior_image rfl hinj hx
    · intro y hy
      let x := e.symm ⟨y, interior_subset hy⟩
      have hex : (e x : ℝ × ℝ) = y := congrArg Subtype.val (e.apply_symm_apply _)
      have hx : (x : ℝ × ℝ) ∈ interior (base r) :=
        (he.mem_interior_iff rfl x).mp (hex.symm ▸ hy)
      exact ⟨x, hx, (hef x).symm.trans hex⟩
  apply inter_image_rectangle_eq_half_of_open_image hr hf.continuousOn ?_ hD hreg hfront
  rw [← hint, himage]
  exact isOpen_interior

end Geometry

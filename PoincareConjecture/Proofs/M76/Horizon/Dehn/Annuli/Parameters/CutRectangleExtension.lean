import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.FourIntervalDiskChart










set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "I" => Icc (0 : ℝ) 1
local notation "P2" => (ℝ × ℝ)

theorem exists_finitePL_cut_rectangle_extension
    (e₀ e₁ : I ≃ₜ I) (he₀ : e₀.IsFinitePL) (he₁ : e₁.IsFinitePL)
    (h₀₀ : (e₀ ⟨0, by norm_num⟩ : ℝ) = 0)
    (h₀₁ : (e₀ ⟨1, by norm_num⟩ : ℝ) = 1)
    (h₁₀ : (e₁ ⟨0, by norm_num⟩ : ℝ) = 0)
    (h₁₁ : (e₁ ⟨1, by norm_num⟩ : ℝ) = 1) :
    ∃ H : (I ×ˢ I : Set P2) ≃ₜ (I ×ˢ I : Set P2), H.IsFinitePL ∧
      (∀ t : I, (H ⟨(t, 0), t.property, by norm_num⟩ : P2) = ((e₀ t : ℝ), 0)) ∧
      (∀ t : I, (H ⟨(t, 1), t.property, by norm_num⟩ : P2) = ((e₁ t : ℝ), 1)) ∧
      (∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) = (0, (t : ℝ))) ∧
      (∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) = (1, (t : ℝ))) := by
  have hI := isFinitePLBallPair_Icc zero_lt_one
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ := hI
  have hid : (Homeomorph.refl I).IsFinitePL :=
    ⟨id, ⟨K, hK, hKI, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩,
      fun _ ↦ rfl⟩
  have horizontal (c : ℝ) : ∃ j : I ≃ₜ (I ×ˢ {c} : Set P2), j.IsFinitePL ∧
      ∀ t : I, (j t : P2) = ((t : ℝ), c) := by
    obtain ⟨j, hj, hv⟩ := hid.exists_horizontal_interval_chart c
    refine ⟨j.symm, hj.symm, fun t ↦ Prod.ext ?_ (j.symm t).property.2⟩
    exact (hv (j.symm t)).symm.trans (congrArg Subtype.val (j.apply_symm_apply t))
  have vertical (c : ℝ) : ∃ j : I ≃ₜ ({c} ×ˢ I : Set P2), j.IsFinitePL ∧
      ∀ t : I, (j t : P2) = (c, (t : ℝ)) := by
    obtain ⟨j, hj, hv⟩ := hid.exists_vertical_interval_chart c
    refine ⟨j.symm, hj.symm, fun t ↦ Prod.ext (j.symm t).property.1 ?_⟩
    exact (hv (j.symm t)).symm.trans (congrArg Subtype.val (j.apply_symm_apply t))
  obtain ⟨b, hb, hbv⟩ := horizontal 0
  obtain ⟨t, ht, htv⟩ := horizontal 1
  obtain ⟨l, hl, hlv⟩ := vertical 0
  obtain ⟨r, hr, hrv⟩ := vertical 1
  have hbox : IsFinitePLBallPair P2 (I ×ˢ I : Set P2)
      (((I ×ˢ {0}) ∪ (I ×ˢ {1})) ∪ (({0} ×ˢ I) ∪ ({1} ×ˢ I))) := by
    have hh := (isFinitePLBallPair_Icc zero_lt_one).prod
      (isFinitePLBallPair_Icc zero_lt_one)
    convert hh using 1
    ext z
    simp only [mem_union, mem_prod, mem_insert_iff, mem_singleton_iff]
    tauto
  obtain ⟨H, hH, hB, hT, hL, hR⟩ := exists_four_interval_disk_chart hbox
    (a := (0, 0)) (b := (1, 0)) (c := (0, 1)) (d := (1, 1))
    (e₀.trans b) (e₁.trans t) l r (he₀.trans hb) (he₁.trans ht) hl hr
    ((hbv (e₀ ⟨0, by norm_num⟩)).trans (Prod.ext h₀₀ rfl))
    ((hbv (e₀ ⟨1, by norm_num⟩)).trans (Prod.ext h₀₁ rfl))
    ((htv (e₁ ⟨0, by norm_num⟩)).trans (Prod.ext h₁₀ rfl))
    ((htv (e₁ ⟨1, by norm_num⟩)).trans (Prod.ext h₁₁ rfl))
    (hlv ⟨0, by norm_num⟩) (hlv ⟨1, by norm_num⟩)
    (hrv ⟨0, by norm_num⟩) (hrv ⟨1, by norm_num⟩)
    (by apply disjoint_left.mpr; rintro z ⟨_, hz⟩ ⟨_, hz'⟩; exact zero_ne_one (hz.symm.trans hz'))
    (by apply disjoint_left.mpr; rintro z ⟨hz, _⟩ ⟨hz', _⟩; exact zero_ne_one (hz.symm.trans hz'))
    (by ext ⟨x, y⟩; simp only [mem_inter_iff, mem_prod, mem_singleton_iff, Prod.mk.injEq]; aesop)
    (by ext ⟨x, y⟩; simp only [mem_inter_iff, mem_prod, mem_singleton_iff, Prod.mk.injEq]; aesop)
    (by ext ⟨x, y⟩; simp only [mem_inter_iff, mem_prod, mem_singleton_iff, Prod.mk.injEq]; aesop)
    (by ext ⟨x, y⟩; simp only [mem_inter_iff, mem_prod, mem_singleton_iff, Prod.mk.injEq]; aesop)
  exact ⟨H, hH, fun x ↦ (hB x).trans (hbv (e₀ x)),
    fun x ↦ (hT x).trans (htv (e₁ x)), fun x ↦ (hL x).trans (hlv x),
    fun x ↦ (hR x).trans (hrv x)⟩

end PoincareConjecture.M76.Dehn

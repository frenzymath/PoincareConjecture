import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.CylinderLevels

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "Cyl" => (Q ×ˢ I : Set (V2 × ℝ))

private theorem exists_unit_interval_rescale (a b : ℝ) (hb : b = a + 1) :
    ∃ h : Icc a b ≃ₜ I, h.IsFinitePL ∧
      ∀ t, (h t : ℝ) = 2 * (t.val - a) - 1 := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show a < b by linarith)
  let f : ℝ →ᴬ[ℝ] ℝ := (2 : ℝ) • ContinuousAffineMap.id ℝ ℝ +
    ContinuousAffineMap.const ℝ ℝ (-2 * a - 1)
  have hfval (t : ℝ) : f t = 2 * (t - a) - 1 := by
    change 2 * t + (-2 * a - 1) = _
    ring
  have hf : FinitePiecewiseAffineOn f (Icc a b) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine f⟩
  have himage : f '' Icc a b = I := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hfval]
      constructor <;> linarith [ht.1, ht.2]
    · intro hy
      refine ⟨a + (y + 1) / 2, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
      rw [hfval]
      ring
  have hi : InjOn f (Icc a b) := by
    intro t _ u _ h
    rw [hfval, hfval] at h
    linarith
  obtain ⟨h, hh, hv⟩ := hf.exists_homeomorph_image hi
  refine ⟨h.trans (Homeomorph.setCongr himage), hh.setCongr rfl himage, ?_⟩
  intro t
  exact (hv t).trans (hfval t)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_cylinder_end_gluing {A B : Set E}
    (a : Cyl ≃ₜ A) (b : Cyl ≃ₜ B) (ha : a.IsFinitePL) (hb : b.IsFinitePL)
    (hab : ∀ x : Cyl, (a x : E) ∈ B ↔ x.val.2 = 1)
    (hba : ∀ x : Cyl, (b x : E) ∈ A ↔ x.val.2 = -1) :
    ∃ (H : Cyl ≃ₜ (A ∪ B : Set E)) (q : Q ≃ₜ Q), H.IsFinitePL ∧ q.IsFinitePL ∧
      (∀ u : Q, (H ⟨(u, -1), u.property, le_rfl, by norm_num⟩ : E) =
        a ⟨(u, -1), u.property, le_rfl, by norm_num⟩) ∧
      (∀ u : Q, (H ⟨(u, 1), u.property, by norm_num, le_rfl⟩ : E) =
        b ⟨(q u, 1), (q u).property, by norm_num, le_rfl⟩) := by
  obtain ⟨q, hq, hqv⟩ := exists_cylinder_end_comparison a b ha hb hab hba
  obtain ⟨l, hl, hlv⟩ := exists_unit_interval_rescale (-1) 0 (by norm_num)
  obtain ⟨r, hr, hrv⟩ := exists_unit_interval_rescale 0 1 (by norm_num)
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  have hid : (Homeomorph.refl Q).IsFinitePL :=
    ⟨id, ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩,
      fun _ ↦ rfl⟩
  let L := (Homeomorph.Set.prod Q (Icc (-1 : ℝ) 0)).trans
    (((Homeomorph.refl Q).prodCongr l).trans (Homeomorph.Set.prod Q I).symm)
  let R := (Homeomorph.Set.prod Q (Icc (0 : ℝ) 1)).trans
    ((q.prodCongr r).trans (Homeomorph.Set.prod Q I).symm)
  have hL : L.IsFinitePL := hid.prod hl
  have hR : R.IsFinitePL := hq.prod hr
  have hLv (x : Q ×ˢ Icc (-1 : ℝ) 0) : (L x).val = (x.val.1, 2 * x.val.2 + 1) := by
    refine Prod.ext ?_ ?_
    · rfl
    change (l ⟨x.val.2, x.property.2⟩ : ℝ) = _
    rw [hlv]
    ring
  have hRv (x : Q ×ˢ Icc (0 : ℝ) 1) :
      (R x).val = ((q ⟨x.val.1, x.property.1⟩ : V2), 2 * x.val.2 - 1) := by
    refine Prod.ext ?_ ?_
    · rfl
    change (r ⟨x.val.2, x.property.2⟩ : ℝ) = _
    simpa only [sub_zero] using hrv ⟨x.val.2, x.property.2⟩
  have hoverlap (x : Q ×ˢ Icc (-1 : ℝ) 0) :
      x.val ∈ Q ×ˢ Icc (0 : ℝ) 1 ↔ (a (L x) : E) ∈ B := by
    rw [hab, hLv]
    change (x.val.1 ∈ Q ∧ 0 ≤ x.val.2 ∧ x.val.2 ≤ 1) ↔ 2 * x.val.2 + 1 = 1
    constructor
    · intro h
      linarith [h.2.1, x.property.2.2]
    · intro h
      exact ⟨x.property.1, by linarith, by linarith⟩
  have hagree (x : V2 × ℝ) (hxl : x ∈ Q ×ˢ Icc (-1 : ℝ) 0)
      (hxr : x ∈ Q ×ˢ Icc (0 : ℝ) 1) :
      (a (L ⟨x, hxl⟩) : E) = b (R ⟨x, hxr⟩) := by
    have hx : x.2 = 0 := le_antisymm hxl.2.2 hxr.2.1
    have hle : L ⟨x, hxl⟩ = ⟨(x.1, 1), hxl.1, by norm_num, le_rfl⟩ := by
      apply Subtype.ext
      exact (hLv _).trans (Prod.ext rfl (by dsimp; linarith))
    have hre : R ⟨x, hxr⟩ =
        ⟨(q ⟨x.1, hxl.1⟩, -1), (q _).property, le_rfl, by norm_num⟩ := by
      apply Subtype.ext
      exact (hRv _).trans (Prod.ext rfl (by dsimp; linarith))
    rw [hle, hre]
    exact (hqv ⟨x.1, hxl.1⟩).symm
  obtain ⟨G, hG, hGl, hGr⟩ := Homeomorph.exists_union_finitePL (L.trans a) (R.trans b)
    (hL.trans ha) (hR.trans hb) hoverlap hagree
  have hunion : (Q ×ˢ Icc (-1 : ℝ) 0) ∪ (Q ×ˢ Icc (0 : ℝ) 1) = Cyl := by
    ext x
    simp only [mem_union, mem_prod, mem_Icc]
    constructor
    · rintro (h | h) <;> exact ⟨h.1, by linarith [h.2.1], by linarith [h.2.2]⟩
    · rintro ⟨hx, hlow, hupp⟩
      rcases le_total x.2 0 with h | h
      · exact Or.inl ⟨hx, hlow, h⟩
      · exact Or.inr ⟨hx, h, hupp⟩
  let H := (Homeomorph.setCongr hunion.symm).trans G
  refine ⟨H, q, hG.setCongr hunion rfl, hq, ?_, ?_⟩
  · intro u
    have h := hGl ⟨(u, -1), u.property, le_rfl, by norm_num⟩
    change (H ⟨(u, -1), u.property, le_rfl, by norm_num⟩ : E) =
      a (L ⟨(u, -1), u.property, le_rfl, by norm_num⟩) at h
    refine h.trans (congrArg (fun x : Cyl ↦ (a x : E)) (Subtype.ext ?_))
    rw [hLv]
    norm_num
  · intro u
    have h := hGr ⟨(u, 1), u.property, by norm_num, le_rfl⟩
    change (H ⟨(u, 1), u.property, by norm_num, le_rfl⟩ : E) =
      b (R ⟨(u, 1), u.property, by norm_num, le_rfl⟩) at h
    refine h.trans (congrArg (fun x : Cyl ↦ (b x : E)) (Subtype.ext ?_))
    rw [hRv]
    norm_num

end PoincareConjecture.M76.Dehn.Annuli

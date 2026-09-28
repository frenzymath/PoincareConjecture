import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.CylinderLevels

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "J" => Icc (-1 : ℝ) 1
local notation "Cyl" => (Q ×ˢ J : Set (V2 × ℝ))

theorem exists_cylinder_band_chart (q : Q ≃ₜ Q) (hq : q.IsFinitePL)
    (a b : ℝ) (hab : a < b) :
    ∃ H : Cyl ≃ₜ (Q ×ˢ Icc a b : Set (V2 × ℝ)), H.IsFinitePL ∧
      ∀ x : Cyl, (H x).val =
        ((q ⟨x.val.1, x.property.1⟩ : V2), a + (b - a) * (x.val.2 + 1) / 2) := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  let f : ℝ →ᴬ[ℝ] ℝ := ((b - a) / 2) • ContinuousAffineMap.id ℝ ℝ +
    ContinuousAffineMap.const ℝ ℝ (a + (b - a) / 2)
  have hfval (t : ℝ) : f t = a + (b - a) * (t + 1) / 2 := by
    change (b - a) / 2 * t + (a + (b - a) / 2) = _
    ring
  have hf : FinitePiecewiseAffineOn f J :=
    ⟨K, hK, hKs, K.affineOnFaces_affine f⟩
  have himage : f '' J = Icc a b := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [hfval]
      constructor <;> nlinarith [ht.1, ht.2]
    · intro hy
      refine ⟨2 * (y - a) / (b - a) - 1, ?_, ?_⟩
      · constructor
        · have := div_nonneg (by linarith [hy.1] : 0 ≤ 2 * (y - a))
            (sub_pos.mpr hab).le
          linarith
        · have := (div_le_iff₀ (sub_pos.mpr hab)).mpr
            (show 2 * (y - a) ≤ 2 * (b - a) by linarith [hy.2])
          linarith
      · rw [hfval]
        field_simp [ne_of_gt (sub_pos.mpr hab)]
        ring
  have hinj : InjOn f J := by
    intro t _ u _ heq
    rw [hfval, hfval] at heq
    nlinarith [sub_pos.mpr hab]
  obtain ⟨r, hr, hrv⟩ := hf.exists_homeomorph_image hinj
  let r' := r.trans (Homeomorph.setCongr himage)
  have hr' : r'.IsFinitePL := hr.setCongr rfl himage
  let H := (Homeomorph.Set.prod Q J).trans
    ((q.prodCongr r').trans (Homeomorph.Set.prod Q (Icc a b)).symm)
  refine ⟨H, hq.prod hr', ?_⟩
  intro x
  refine Prod.ext rfl ?_
  exact (hrv ⟨x.val.2, x.property.2⟩).trans (hfval x.val.2)

theorem finitePL_square_rim_refl : (Homeomorph.refl Q).IsFinitePL := by
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  exact ⟨id, ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩,
    fun _ ↦ rfl⟩

end PoincareConjecture.M76.Dehn.Annuli

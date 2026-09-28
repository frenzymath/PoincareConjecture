import PoincareConjecture.Proofs.M76.Mathlib.SquareShellSector










set_option autoImplicit false

open Set Geometry

namespace SquareShell



noncomputable def radiusMap (a b c d r : ℝ) : ℝ :=
  c + ((d - c) / (b - a)) * (r - a)



theorem strictMono_radiusMap {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    StrictMono (radiusMap a b c d) := by
  have hpos : 0 < (d - c) / (b - a) := div_pos (sub_pos.mpr hcd) (sub_pos.mpr hab)
  intro r s hrs
  dsimp [radiusMap]
  simpa only [add_comm] using
    add_lt_add_left (mul_lt_mul_of_pos_left (sub_lt_sub_right hrs a) hpos) c



theorem radiusMap_endpoints {a b c d : ℝ} (hab : a < b) :
    radiusMap a b c d a = c ∧ radiusMap a b c d b = d := by
  constructor
  · simp [radiusMap]
  · unfold radiusMap
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
    ring



theorem radiusMap_image {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    radiusMap a b c d '' Icc a b = Icc c d := by
  have hc : Continuous (radiusMap a b c d) := by unfold radiusMap; fun_prop
  rw [hc.continuousOn.image_Icc_of_monotoneOn hab.le
    ((strictMono_radiusMap hab hcd).monotone.monotoneOn _),
    (radiusMap_endpoints (c := c) (d := d) hab).1,
    (radiusMap_endpoints (c := c) (d := d) hab).2]




theorem exists_parameter_radius_homeomorph {a b c d : ℝ}
    (hab : a < b) (hcd : c < d) :
    ∃ D : parameterRectangle a b ≃ₜ parameterRectangle c d,
      D.IsFinitePL ∧ ∀ p, (D p : ℝ × ℝ) =
        ((p : ℝ × ℝ).1, radiusMap a b c d (p : ℝ × ℝ).2) := by
  let x := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let y := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  let G : (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
    x.prod (ContinuousAffineMap.const ℝ (ℝ × ℝ) c +
      ((d - c) / (b - a)) • (y - ContinuousAffineMap.const ℝ (ℝ × ℝ) a))
  have hGval (p : ℝ × ℝ) : G p = (p.1, radiusMap a b c d p.2) := rfl
  have hGinj : Function.Injective G := by
    intro p q he
    have hs := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    change p.1 = q.1 at hs
    change radiusMap a b c d p.2 = radiusMap a b c d q.2 at hr
    exact Prod.ext hs ((strictMono_radiusMap hab hcd).injective hr)
  have hGimage : G '' parameterRectangle a b = parameterRectangle c d := by
    change Prod.map id (radiusMap a b c d) '' (Icc 0 1 ×ˢ Icc a b) = Icc 0 1 ×ˢ Icc c d
    rw [prodMap_image_prod, image_id, radiusMap_image hab hcd]
  have hex := PLStrip.exists_segmentProduct_homeomorph
    (show (0 : ℝ) ≠ 1 by norm_num) hab
  rw [segment_eq_Icc zero_le_one] at hex
  obtain ⟨D, hD, _⟩ := hex
  obtain ⟨_, ⟨K, hK, hKS, _⟩, _⟩ := hD.symm
  have hPL : FinitePiecewiseAffineOn G (parameterRectangle a b) :=
    ⟨K, hK, hKS, K.affineOnFaces_affine G⟩
  have he := hPL.exists_homeomorph_image hGinj.injOn
  rw [hGimage] at he
  obtain ⟨E, hE, hEval⟩ := he
  exact ⟨E, hE, fun p => (hEval p).trans (hGval p)⟩

end SquareShell

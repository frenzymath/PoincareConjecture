import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals










set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_finitePL_segment_height_chart
    (A : E →ᵃ[ℝ] ℝ) {x y : E} {α β : ℝ}
    (hαβ : α < β) (hx : A x = α) (hy : A y = β) :
    ∃ d : Icc α β ≃ₜ segment ℝ x y, d.IsFinitePL ∧
      (∀ t, A (d t) = (t : ℝ)) ∧
      (d ⟨α, ⟨le_rfl, hαβ.le⟩⟩ : E) = x ∧
      (d ⟨β, ⟨hαβ.le, le_rfl⟩⟩ : E) = y := by
  have hxy : x ≠ y := by
    intro heq
    have h := congrArg A heq
    rw [hx, hy] at h
    exact hαβ.ne h
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  let f : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.lineMap x y
  let g : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.lineMap α β
  have hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine f⟩
  have hg : FinitePiecewiseAffineOn g (Icc (0 : ℝ) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine g⟩
  have hfimage : f '' Icc (0 : ℝ) 1 = segment ℝ x y := by
    change AffineMap.lineMap (k := ℝ) x y '' Icc (0 : ℝ) 1 = segment ℝ x y
    exact (segment_eq_image_lineMap ℝ x y).symm
  have hgimage : g '' Icc (0 : ℝ) 1 = Icc α β := by
    change AffineMap.lineMap (k := ℝ) α β '' Icc (0 : ℝ) 1 = Icc α β
    rw [← segment_eq_image_lineMap, segment_eq_Icc hαβ.le]
  have hFexists := hf.exists_homeomorph_image (lineMap_injective ℝ hxy).injOn
  rw [hfimage] at hFexists
  obtain ⟨F, hF, hFval⟩ := hFexists
  have hGexists := hg.exists_homeomorph_image (lineMap_injective ℝ hαβ.ne).injOn
  rw [hgimage] at hGexists
  obtain ⟨G, hG, hGval⟩ := hGexists
  have hG0 : G ⟨0, ⟨le_rfl, zero_le_one⟩⟩ = ⟨α, ⟨le_rfl, hαβ.le⟩⟩ := by
    apply Subtype.ext
    rw [hGval]
    exact lineMap_apply_zero α β
  have hG1 : G ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = ⟨β, ⟨hαβ.le, le_rfl⟩⟩ := by
    apply Subtype.ext
    rw [hGval]
    exact lineMap_apply_one α β
  refine ⟨G.symm.trans F, hG.symm.trans hF, ?_, ?_, ?_⟩
  · intro t
    change A (F (G.symm t)) = (t : ℝ)
    rw [hFval]
    change A (AffineMap.lineMap x y (G.symm t : ℝ)) = (t : ℝ)
    rw [A.apply_lineMap, hx, hy]
    simpa only [g, ContinuousAffineMap.coe_lineMap_eq, G.apply_symm_apply]
      using (hGval (G.symm t)).symm
  · change (F (G.symm ⟨α, ⟨le_rfl, hαβ.le⟩⟩) : E) = x
    rw [← hG0, G.symm_apply_apply, hFval]
    exact lineMap_apply_zero x y
  · change (F (G.symm ⟨β, ⟨hαβ.le, le_rfl⟩⟩) : E) = y
    rw [← hG1, G.symm_apply_apply, hFval]
    exact lineMap_apply_one x y

end AffineMap

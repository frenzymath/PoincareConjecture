import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.ConvexFrontierSubcomplex










set_option autoImplicit false

open Set Geometry

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePLBallPair.exists_unitInterval_chart_with_endpoints
    {s : Set E} {a b : E} (hs : IsFinitePLBallPair ℝ s {a, b}) (hab : a ≠ b) :
    ∃ e : Icc (0 : ℝ) 1 ≃ₜ s, e.IsFinitePL ∧
      (e ⟨0, ⟨le_rfl, zero_le_one⟩⟩ : E) = a ∧
      (e ⟨1, ⟨zero_le_one, le_rfl⟩⟩ : E) = b := by
  have hI := isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)
  have hcopy := hI
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ := hcopy
  let J := K.frontierSubcomplex (Icc (0 : ℝ) 1)
  have hJ : J.faces.Finite := K.frontierSubcomplex_finite _ hK
  have hJs : J.space = ({0, 1} : Set ℝ) := by
    rw [K.frontierSubcomplex_space isClosed_Icc (convex_Icc _ _)
      (by rw [interior_Icc]; exact nonempty_Ioo.mpr zero_lt_one) hKI,
      frontier_Icc zero_le_one]
  let f : ℝ →ᴬ[ℝ] E := ContinuousAffineMap.lineMap a b
  have hf : FinitePiecewiseAffineOn f ({0, 1} : Set ℝ) :=
    ⟨J, hJ, hJs, J.affineOnFaces_affine f⟩
  have hfinj : InjOn f ({0, 1} : Set ℝ) := (AffineMap.lineMap_injective ℝ hab).injOn
  have himage : f '' ({0, 1} : Set ℝ) = {a, b} := by
    have hzero : f (0 : ℝ) = a := by
      dsimp only [f]
      change AffineMap.lineMap (k := ℝ) a b (0 : ℝ) = a
      exact AffineMap.lineMap_apply_zero a b
    have hone : f (1 : ℝ) = b := by
      dsimp only [f]
      change AffineMap.lineMap (k := ℝ) a b (1 : ℝ) = b
      exact AffineMap.lineMap_apply_one a b
    simp only [image_pair, hzero, hone]
  obtain ⟨F, hF, hFval⟩ := hf.exists_homeomorph_image hfinj
  let d := F.trans (Homeomorph.setCongr himage)
  have hd : d.IsFinitePL := ⟨f, hf, fun x => hFval x⟩
  obtain ⟨e, he, hboundary, _⟩ := hI.exists_extension hs d hd
  refine ⟨e, he, ?_, ?_⟩
  · have h := congrArg Subtype.val (hboundary ⟨0, by simp⟩)
    change (e ⟨0, _⟩ : E) = (F ⟨0, _⟩ : E) at h
    exact h.trans ((hFval ⟨0, by simp⟩).trans (AffineMap.lineMap_apply_zero a b))
  · have h := congrArg Subtype.val (hboundary ⟨1, by simp⟩)
    change (e ⟨1, _⟩ : E) = (F ⟨1, _⟩ : E) at h
    exact h.trans ((hFval ⟨1, by simp⟩).trans (AffineMap.lineMap_apply_one a b))

end Set

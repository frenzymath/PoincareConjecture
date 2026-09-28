import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear










set_option autoImplicit false

open Set Geometry

namespace ContinuousLinearMap




theorem exists_two_halfspace_shear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (ell : E →L[ℝ] ℝ) (a b : E) (ha : ell a = 0) (hb : ell b = 0) :
    ∃ H : E ≃ₜ E, H.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E ∧
      (∀ x, H x = x - min (ell x) 0 • a - max (ell x) 0 • b) ∧
      (∀ x, H.symm x = x + min (ell x) 0 • a + max (ell x) 0 • b) ∧
      ∀ x, ell (H x) = ell x := by
  let F : E → E := fun x => x - min (ell x) 0 • a - max (ell x) 0 • b
  let G : E → E := fun x => x + min (ell x) 0 • a + max (ell x) 0 • b
  have hFell (x : E) : ell (F x) = ell x := by
    simp only [F, map_sub, map_smul, ha, hb, smul_zero, sub_zero]
  have hGell (x : E) : ell (G x) = ell x := by
    simp only [G, map_add, map_smul, ha, hb, smul_zero, add_zero]
  let H : E ≃ₜ E :=
    { toFun := F
      invFun := G
      left_inv := by
        intro x
        change F x + min (ell (F x)) 0 • a + max (ell (F x)) 0 • b = x
        rw [hFell]
        dsimp only [F]
        abel
      right_inv := by
        intro x
        change G x - min (ell (G x)) 0 • a - max (ell (G x)) 0 • b = x
        rw [hGell]
        dsimp only [G]
        abel
      continuous_toFun :=
        (continuous_id.sub ((ell.continuous.min continuous_const).smul continuous_const)).sub
          ((ell.continuous.max continuous_const).smul continuous_const)
      continuous_invFun :=
        (continuous_id.add ((ell.continuous.min continuous_const).smul continuous_const)).add
          ((ell.continuous.max continuous_const).smul continuous_const) }
  have hfinite (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
      FinitePiecewiseAffineOn F K.space := by
    have hid := (K.affineOnFaces_affine
      (ContinuousAffineMap.id ℝ E)).finitePiecewiseAffineOn hK
    have hl := (K.affineOnFaces_affine ell.toContinuousAffineMap).finitePiecewiseAffineOn hK
    have hz := (K.affineOnFaces_affine
      (ContinuousAffineMap.const ℝ E (0 : ℝ))).finitePiecewiseAffineOn hK
    have hm : FinitePiecewiseAffineOn (fun x => min (ell x) 0 • a) K.space :=
      ((hl.min hz).postcomp
        ((ContinuousLinearMap.id ℝ ℝ).smulRight a).toContinuousAffineMap).congr (fun _ _ => rfl)
    have hp : FinitePiecewiseAffineOn (fun x => max (ell x) 0 • b) K.space :=
      ((hl.max hz).postcomp
        ((ContinuousLinearMap.id ℝ ℝ).smulRight b).toContinuousAffineMap).congr (fun _ _ => rfl)
    exact (hid.sub hm).sub hp
  refine ⟨H, ?_, fun _ => rfl, fun _ => rfl, hFell⟩
  apply (mem_piecewiseAffineGroupoid_iff_forward H.toOpenPartialHomeomorph).mpr
  intro x _
  obtain ⟨K, hK, hxK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed isCompact_singleton
      isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
  obtain ⟨J, hJ, hJK, hPL⟩ := hfinite K hK
  refine ⟨J, hJ, ?_, fun _ _ => mem_univ _, ?_⟩
  · rw [hJK]
    exact hxK (mem_singleton x)
  · exact hPL

end ContinuousLinearMap

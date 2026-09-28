import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

private theorem affine_mem_interval {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    2 * N.epsilon⁻¹ * t - N.epsilon⁻¹ ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
  have hpos := inv_pos.mpr N.epsilon_pos
  constructor <;> nlinarith [ht.1, ht.2]

private noncomputable def intervalHomeomorph :
    Set.Ioo (0 : ℝ) 1 ≃ₜ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
  (affineHomeomorph (2 * N.epsilon⁻¹) (-N.epsilon⁻¹)
    (mul_ne_zero (by norm_num) (inv_ne_zero N.epsilon_pos.ne'))).subtype (by
      intro t
      change t ∈ Set.Ioo (0 : ℝ) 1 ↔
        2 * N.epsilon⁻¹ * t + -N.epsilon⁻¹ ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹
      have hpos := inv_pos.mpr N.epsilon_pos
      constructor
      · exact N.affine_mem_interval
      · rintro ⟨hlo, hhi⟩
        constructor <;> nlinarith)



noncomputable def m25_openCylinderModel : OpenCylinderModel N.carrier where
  homeomorph := ((Homeomorph.refl UnitTwoSphere).prodCongr N.intervalHomeomorph).trans
    N.coordinate
  coordinate z := N.coordinate_map (z.1, 2 * N.epsilon⁻¹ * z.2 - N.epsilon⁻¹)
  coordinate_eq z := N.coordinate_map_eq (z.1, N.intervalHomeomorph z.2)
  coordinate_smooth := by
    apply N.coordinate_map_smooth.comp
    · have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
          (fun t : ℝ => 2 * N.epsilon⁻¹ * t - N.epsilon⁻¹) :=
        ((contDiff_const.mul contDiff_id).sub contDiff_const).contMDiff
      exact contMDiffOn_fst.prodMk (h.comp_contMDiffOn contMDiffOn_snd)
    · intro z hz
      exact ⟨Set.mem_univ _, N.affine_mem_interval hz.2⟩
  inverse x := ((N.coordinate_inverse x).1,
    ((N.coordinate_inverse x).2 + N.epsilon⁻¹) / (2 * N.epsilon⁻¹))
  inverse_mem x hx := by
    have hs := (N.coordinate_inverse_mem x hx).2
    have hpos := inv_pos.mpr N.epsilon_pos
    refine ⟨Set.mem_univ _, ?_, ?_⟩
    · exact div_pos (by linarith [hs.1]) (by positivity)
    · apply (div_lt_one (by positivity : (0 : ℝ) < 2 * N.epsilon⁻¹)).mpr
      linarith [hs.2]
  left_inverse := by
    intro z hz
    dsimp only
    rw [N.coordinate_inverse_map _ (N.affine_mem_interval hz.2)]
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [N.epsilon_pos.ne']
      ring
  right_inverse := by
    intro x hx
    have heq : 2 * N.epsilon⁻¹ *
        (((N.coordinate_inverse x).2 + N.epsilon⁻¹) / (2 * N.epsilon⁻¹)) -
          N.epsilon⁻¹ = (N.coordinate_inverse x).2 := by
      field_simp [N.epsilon_pos.ne']
      ring
    dsimp only
    rw [heq]
    exact N.coordinate_map_inverse hx
  inverse_smooth := by
    have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun t : ℝ => (t + N.epsilon⁻¹) / (2 * N.epsilon⁻¹)) :=
      ((contDiff_id.add contDiff_const).div_const _).contMDiff
    intro x hx
    exact (N.coordinate_inverse_smooth x hx).fst.prodMk
      (h.contMDiffAt.comp_contMDiffWithinAt x (N.coordinate_inverse_smooth x hx).snd)



theorem m25_openCylinderModel_middleSphere :
    N.m25_openCylinderModel.middleSphere = N.central_sphere := by
  rw [N.central_sphere_eq]
  change (fun z : RoundCylinderSpace =>
    N.coordinate_map (z.1, 2 * N.epsilon⁻¹ * z.2 - N.epsilon⁻¹)) ''
      (Set.univ ×ˢ ({1 / 2} : Set ℝ)) =
        N.coordinate_map '' (Set.univ ×ˢ ({0} : Set ℝ))
  ext x
  have hmid : 2 * N.epsilon⁻¹ * (1 / 2) - N.epsilon⁻¹ = 0 := by ring
  constructor
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    have ht' : t = 1 / 2 := ht
    subst t
    refine ⟨(q, 0), ⟨Set.mem_univ _, rfl⟩, ?_⟩
    dsimp only
    rw [hmid]
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    have ht' : t = 0 := ht
    subst t
    refine ⟨(q, 1 / 2), ⟨Set.mem_univ _, rfl⟩, ?_⟩
    dsimp only
    rw [hmid]

end PoincareConjecture.EpsilonNeck

import PoincareLib.Topology.Manifold.ConnectedSum.Surgery.Topology

/-!
# Shortening an actual smooth collar by one common positive factor

Composition with (z,s) -> (z,a*s) retains the original collar and
uses its actual inverse followed by division by a. The normalized
source and full image are proved, including the unchanged central sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable {A : GeneralizedSliceCarrier.{u}}
  (c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace A.carrier ∞)

/-- The same collar with its signed parameter multiplied by the supplied scale. -/
noncomputable def shortCollar (a : ℝ) (z : RoundCylinderSpace) : A.carrier :=
  c (z.1, a * z.2)

/-- The same actual collar inverse with its signed parameter divided by that scale. -/
noncomputable def shortCollarInverse (a : ℝ) (x : A.carrier) : RoundCylinderSpace :=
  ((c.symm x).1, (c.symm x).2 / a)

variable {ε a : ℝ} (ha : 0 < a) (haε : a ≤ ε)
  (hc : c.source = Set.univ ×ˢ Set.Ioo (-ε) ε)

include ha haε hc

/-- Every normalized collar coordinate has its scaled coordinate in the actual original source. -/
theorem shortCollar_source {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) : (z.1, a * z.2) ∈ c.source := by
  rw [hc]
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · have h := mul_lt_mul_of_pos_left hz.2.1 ha
    nlinarith
  · have h := mul_lt_mul_of_pos_left hz.2.2 ha
    nlinarith

/-- The inverse of the shortened collar recovers every original normalized coordinate. -/
theorem shortCollar_left_inverse :
    Set.LeftInvOn (shortCollarInverse c a) (shortCollar c a)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  intro z hz
  change ((c.symm (c (z.1, a * z.2))).1, (c.symm (c (z.1, a * z.2))).2 / a) = z
  have hleft := c.toPartialEquiv.left_inv
    (shortCollar_source c ha haε hc hz)
  change ((c.toPartialEquiv.symm (c.toPartialEquiv (z.1, a * z.2))).1,
    (c.toPartialEquiv.symm (c.toPartialEquiv (z.1, a * z.2))).2 / a) = z
  rw [hleft]
  apply Prod.ext
  · rfl
  · exact mul_div_cancel_left₀ z.2 ha.ne'

/-- Every point of the actual image is recovered by the same forward and inverse maps. -/
theorem shortCollar_right_inverse :
    Set.LeftInvOn (shortCollar c a) (shortCollarInverse c a)
      (shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rintro _ ⟨z, hz, rfl⟩
  exact congrArg (shortCollar c a) (shortCollar_left_inverse c ha haε hc hz)

/-- The shortened collar image lies in the original actual inverse domain. -/
theorem shortCollar_image_subset :
    shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) ⊆ c.target := by
  rintro _ ⟨z, hz, rfl⟩
  exact c.map_source (shortCollar_source c ha haε hc hz)

/-- Both maps are smooth on the exact domains used by the shortened collar. -/
theorem shortCollar_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (shortCollar c a)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
  c.contMDiffOn_toFun.comp
    (contMDiff_fst.prodMk
      ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd)).contMDiffOn
    (fun _ hz => shortCollar_source c ha haε hc hz)

/-- The literal rescaled inverse is smooth throughout the full shortened image. -/
theorem shortCollarInverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (shortCollarInverse c a)
      (shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
  (contMDiff_fst.prodMk
    ((contDiff_id.div_const a).contMDiff.comp contMDiff_snd)).comp_contMDiffOn
    (c.contMDiffOn_invFun.mono (shortCollar_image_subset c ha haε hc))

omit haε hc in
/-- The full shortened image is exactly the image of the corresponding original interval. -/
theorem shortCollar_image :
    shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) =
      c '' (Set.univ ×ˢ Set.Ioo (-a) a) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨(z.1, a * z.2), ⟨Set.mem_univ _, ?_, ?_⟩, rfl⟩
    · have h := mul_lt_mul_of_pos_left hz.2.1 ha
      nlinarith
    · have h := mul_lt_mul_of_pos_left hz.2.2 ha
      nlinarith
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨(z.1, z.2 / a), ⟨Set.mem_univ _, ?_, ?_⟩, ?_⟩
    · exact (lt_div_iff₀ ha).mpr (by linarith [hz.2.1])
    · exact (div_lt_iff₀ ha).mpr (by linarith [hz.2.2])
    · change c (z.1, a * (z.2 / a)) = c z
      rw [mul_div_cancel₀ _ ha.ne']

/-- Openness comes from restricting the original open partial homeomorphism to an open subcylinder. -/
theorem shortCollar_open :
    IsOpen (shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rw [shortCollar_image c ha]
  apply c.toOpenPartialHomeomorph.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
  intro z hz
  change z ∈ c.source
  rw [hc]
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

omit ha haε hc in
/-- The central sphere is literally unchanged by signed rescaling. -/
theorem shortCollar_central :
    shortCollar c a '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      c '' (Set.univ ×ˢ ({0} : Set ℝ)) := by
  apply Set.image_congr
  intro z hz
  have hz0 : z.2 = 0 := hz.2
  have hzero : a * z.2 = z.2 := by rw [hz0, mul_zero]
  exact congrArg c (Prod.ext rfl hzero)

end PoincareMT.M38

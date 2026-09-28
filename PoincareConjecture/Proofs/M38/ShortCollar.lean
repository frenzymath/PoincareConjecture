import PoincareConjecture.Definitions.Ch15.SurgeryTopology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}
  (c : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace A.carrier ∞)

noncomputable def shortCollar (a : ℝ) (z : RoundCylinderSpace) : A.carrier :=
  c (z.1, a * z.2)

noncomputable def shortCollarInverse (a : ℝ) (x : A.carrier) : RoundCylinderSpace :=
  ((c.symm x).1, (c.symm x).2 / a)

variable {ε a : ℝ} (ha : 0 < a) (haε : a ≤ ε)
  (hc : c.source = Set.univ ×ˢ Set.Ioo (-ε) ε)

include ha haε hc

theorem shortCollar_source {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) : (z.1, a * z.2) ∈ c.source := by
  rw [hc]
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · have h := mul_lt_mul_of_pos_left hz.2.1 ha
    nlinarith
  · have h := mul_lt_mul_of_pos_left hz.2.2 ha
    nlinarith

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

theorem shortCollar_right_inverse :
    Set.LeftInvOn (shortCollar c a) (shortCollarInverse c a)
      (shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rintro _ ⟨z, hz, rfl⟩
  exact congrArg (shortCollar c a) (shortCollar_left_inverse c ha haε hc hz)

theorem shortCollar_image_subset :
    shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) ⊆ c.target := by
  rintro _ ⟨z, hz, rfl⟩
  exact c.map_source (shortCollar_source c ha haε hc hz)

theorem shortCollar_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (shortCollar c a)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
  c.contMDiffOn_toFun.comp
    (contMDiff_fst.prodMk
      ((contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_snd)).contMDiffOn
    (fun _ hz => shortCollar_source c ha haε hc hz)

theorem shortCollarInverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (shortCollarInverse c a)
      (shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
  (contMDiff_fst.prodMk
    ((contDiff_id.div_const a).contMDiff.comp contMDiff_snd)).comp_contMDiffOn
    (c.contMDiffOn_invFun.mono (shortCollar_image_subset c ha haε hc))

omit haε hc in

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

theorem shortCollar_open :
    IsOpen (shortCollar c a '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rw [shortCollar_image c ha]
  apply c.toOpenPartialHomeomorph.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
  intro z hz
  change z ∈ c.source
  rw [hc]
  exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩

omit ha haε hc in

theorem shortCollar_central :
    shortCollar c a '' (Set.univ ×ˢ ({0} : Set ℝ)) =
      c '' (Set.univ ×ˢ ({0} : Set ℝ)) := by
  apply Set.image_congr
  intro z hz
  have hz0 : z.2 = 0 := hz.2
  have hzero : a * z.2 = z.2 := by rw [hz0, mul_zero]
  exact congrArg c (Prod.ext rfl hzero)

end PoincareConjecture.M38

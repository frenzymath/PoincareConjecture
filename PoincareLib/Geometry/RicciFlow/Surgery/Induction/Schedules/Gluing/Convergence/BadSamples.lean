import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Schedules.Gluing.Construction.Conclusion

/-!
# A failed uniform comparison has an older-branch witness

The literal Ricci time join already gives smooth coefficients. Failure
of the contract therefore supplies a finite jet larger than the fixed
positive half-square margin. The recent comparison excludes its branch.
Source: Proposition 15.2, pp. 353-354.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M45

/-- The checked time join supplies the literal spatial smoothness field
throughout the requested cylinder and complete time interval.
Source: Proposition 15.2, pp. 353-354. -/
theorem piecewiseTensor_smooth_on_output {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hbeta_one : beta ≤ 1)
    (hsmall : beta * epsilon < 1 / 2) (I : M45NeckGluingInput.{u} epsilon beta)
    (hduration : 1 ≤ I.older_duration) :
    ∀ t ∈ Ioc (-1 : ℝ) 0, RoundCylinderTensorSmoothOn epsilon
      (I.piecewiseTensor I.recent_patch.coordinate t) := by
  have hpos : 0 < beta * epsilon := mul_pos hbeta hepsilon
  have hle : beta * epsilon ≤ epsilon := by nlinarith
  intro t ht q a b
  apply (I.piecewiseTensor_joint_smooth hpos hsmall q a b).comp
    (contDiffOn_const.prodMk contDiffOn_id)
  intro p hp
  exact ⟨⟨by linarith [ht.1], ht.2⟩, hp.1, cylinderDomain_mono hpos hle hp.2⟩

/-- Once older survival is proved, failure of the literal conclusion
supplies a point where the squared jet exceeds half the output tolerance.
Source: Proposition 15.2, pp. 353-354; GluingCompactness.md. -/
theorem exists_bad_gluing_sample {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hbeta_one : beta ≤ 1)
    (hsmall : beta * epsilon < 1 / 2) (I : M45NeckGluingInput.{u} epsilon beta)
    (hduration : 1 ≤ I.older_duration) (hfail : ¬ Nonempty (M45NeckGluingConclusion I)) :
    ∃ t ∈ Ioc (-1 : ℝ) 0, ∃ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ ∧
        epsilon ^ 2 / 2 < roundCylinderJetErrorSquared t
          (I.piecewiseTensor I.recent_patch.coordinate t) ⌊epsilon⁻¹⌋₊ z := by
  by_contra! h
  apply hfail
  apply gluingConclusion_of_comparison hepsilon hbeta hbeta_one hsmall I hduration
  refine ⟨piecewiseTensor_smooth_on_output hepsilon hbeta hbeta_one hsmall I hduration,
    epsilon ^ 2 / 2, ?_, ?_⟩
  · nlinarith [sq_pos_of_pos hepsilon]
  · exact h

/-- A bad sample lies strictly before the joining time, since the recent
branch has its stronger input tolerance. Source: Proposition 15.2, pp. 353-354. -/
theorem bad_gluing_sample_is_older {epsilon beta t : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hbeta_half : beta ≤ 1 / 2)
    (I : M45NeckGluingInput.{u} epsilon beta) (ht : t ∈ Ioc (-1 : ℝ) 0)
    (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹)
    (hbad : epsilon ^ 2 / 2 < roundCylinderJetErrorSquared t
      (I.piecewiseTensor I.recent_patch.coordinate t) ⌊epsilon⁻¹⌋₊ z) :
    t < -I.recent_duration := by
  by_contra h
  have hjoin : -I.recent_duration ≤ t := le_of_not_gt h
  have hpos : 0 < beta * epsilon := mul_pos hbeta hepsilon
  have hle : beta * epsilon ≤ epsilon := by nlinarith
  have hhalf : beta * epsilon ≤ epsilon / 2 := by nlinarith
  have hsquare := (sq_le_sq₀ hpos.le (by positivity : 0 ≤ epsilon / 2)).mpr hhalf
  have hz' := cylinderDomain_mono hpos hle hz
  have horder : ⌊epsilon⁻¹⌋₊ ≤ ⌊(beta * epsilon)⁻¹⌋₊ :=
    Nat.floor_mono (inv_anti₀ hpos hle)
  obtain ⟨_, bound, hbound, hjet⟩ := I.recent_comparison
  have hupper := (evolvingJetError_mono_order
    (lt_of_le_of_lt ht.2 (by norm_num))
    (roundCylinderPullback (I.recent_flow.metric t) I.recent_patch.coordinate)
    horder z).trans (hjet t ⟨hjoin, ht.2⟩ z hz')
  simp only [M45NeckGluingInput.piecewiseTensor, if_pos hjoin] at hbad
  nlinarith [sq_pos_of_pos hepsilon]

/-- A failed gluing conclusion admits a bad sample in the actual older
branch of the retained coordinates. Source: Proposition 15.2, pp. 353-354. -/
theorem exists_bad_older_sample {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta : 0 < beta) (hbeta_half : beta ≤ 1 / 2)
    (hsmall : beta * epsilon < 1 / 2) (I : M45NeckGluingInput.{u} epsilon beta)
    (hduration : 1 ≤ I.older_duration) (hfail : ¬ Nonempty (M45NeckGluingConclusion I)) :
    ∃ t ∈ Ioc (-1 : ℝ) 0, t < -I.recent_duration ∧ ∃ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ ∧
        epsilon ^ 2 / 2 < roundCylinderJetErrorSquared t
          (I.piecewiseTensor I.recent_patch.coordinate t) ⌊epsilon⁻¹⌋₊ z := by
  obtain ⟨t, ht, z, hz, hbad⟩ := exists_bad_gluing_sample hepsilon hbeta
    (by linarith) hsmall I hduration hfail
  exact ⟨t, ht, bad_gluing_sample_is_older hepsilon hbeta hbeta_half I ht z hz hbad,
    z, hz, hbad⟩

end PoincareMT.M45

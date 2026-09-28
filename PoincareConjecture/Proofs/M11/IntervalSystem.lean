import PoincareConjecture.Proofs.M11.IntervalDifferential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

theorem smoothInterval_inclusion_smooth (I J : SpacetimeInterval)
    (h : I.domain ⊆ J.domain) :
    ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞
      (spacetimeIntervalInclusion (smoothInterval I) (smoothInterval J) h) := by
  let := intervalChartedSpace I
  let := intervalChartedSpace J
  let f := spacetimeIntervalInclusion (smoothInterval I) (smoothInterval J) h
  intro t
  let D := intervalSegmentAt J (f t)
  let : Fact (D.left < D.right) := ⟨D.lt⟩
  let S : Set (smoothInterval I).Point := {s | s.val ∈ D.window}
  have hS : S ∈ 𝓝 t :=
    (D.open_window.preimage continuous_subtype_val).mem_nhds (intervalSegmentAt_mem J (f t))
  have hproj : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞ (D.toSegment ∘ f) S := by
    apply contMDiffOn_projIcc.comp (smoothInterval I).inclusion_smooth.contMDiffOn
    intro s hs
    exact D.window_subset ⟨hs, h s.property⟩
  apply contMDiffAt_iff_target.mpr
  refine ⟨?_, ?_⟩
  · change ContinuousAt (fun s : I.domain ↦ (⟨s.val, h s.property⟩ : J.domain)) t
    fun_prop
  change ContMDiffAt (𝓡∂ 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
    (extChartAt (𝓡∂ 1) (D.toSegment (f t)) ∘ (D.toSegment ∘ f)) t
  exact (contMDiffAt_extChartAt (I := 𝓡∂ 1) (x := D.toSegment (f t))).comp t
    (hproj.contMDiffAt hS)

theorem smoothInterval_inclusion_derivative (I J : SpacetimeInterval)
    (h : I.domain ⊆ J.domain) (t : (smoothInterval I).Point) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1)
      (spacetimeIntervalInclusion (smoothInterval I) (smoothInterval J) h) t
      ((smoothInterval I).positiveTangent t) =
      (smoothInterval J).positiveTangent
        (spacetimeIntervalInclusion (smoothInterval I) (smoothInterval J) h t) := by
  let := intervalChartedSpace I
  let := intervalChartedSpace J
  let f := spacetimeIntervalInclusion (smoothInterval I) (smoothInterval J) h
  apply ((smoothInterval J).inclusionDerivative (f t)).injective
  have hchain := mfderiv_comp_apply t
    (((smoothInterval J).inclusion_smooth (f t)).mdifferentiableAt (by simp))
    ((smoothInterval_inclusion_smooth I J h t).mdifferentiableAt (by simp))
    ((smoothInterval I).positiveTangent t)
  have hnorm : mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val ∘ f) t
      ((smoothInterval I).positiveTangent t) = (1 : ℝ) :=
    ((smoothInterval I).inclusionDerivative t).apply_symm_apply 1
  have hnorm' := ((smoothInterval J).inclusionDerivative (f t)).apply_symm_apply (1 : ℝ)
  exact hchain.symm.trans (hnorm.trans hnorm'.symm)

noncomputable def intervalSystem : SpacetimeIntervalSystem where
  interval := smoothInterval
  inclusion_smooth := smoothInterval_inclusion_smooth
  inclusion_derivative := smoothInterval_inclusion_derivative

end PoincareConjecture.Proofs.M11

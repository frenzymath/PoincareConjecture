import PoincareConjecture.Definitions.M11TimeInterval
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Interval.UniqueDifferential
import PoincareConjecture.Proofs.M12.Analysis.Calculus.InverseWithin
import Mathlib.Geometry.Manifold.MFDeriv.Atlas








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Set Filter

namespace PoincareConjecture.SmoothSpacetimeInterval

noncomputable section

variable {I : SpacetimeInterval}

def realParam (T : SmoothSpacetimeInterval I) (t : ℝ) : T.Point := by
  classical
  exact if ht : t ∈ I.domain then ⟨t, ht⟩ else
    ⟨I.nontrivial.nonempty.choose, I.nontrivial.nonempty.choose_spec⟩

@[simp] theorem realParam_coe (T : SmoothSpacetimeInterval I) (t : T.Point) :
    T.realParam t = t := by
  simp [realParam, t.property]

theorem realParam_val (T : SmoothSpacetimeInterval I) {t : ℝ} (ht : t ∈ I.domain) :
    (T.realParam t).val = t := by simp [realParam, ht]

theorem realParam_continuousOn (T : SmoothSpacetimeInterval I) :
    ContinuousOn T.realParam I.domain := by
  intro t ht
  apply (Topology.IsInducing.continuousWithinAt_iff
    Topology.IsInducing.subtypeVal).mpr
  exact continuousWithinAt_id.congr (fun s hs => T.realParam_val hs)
    (T.realParam_val ht)

private theorem chart_real_invertible (T : SmoothSpacetimeInterval I) (p : T.Point)
    {y : EuclideanSpace ℝ (Fin 1)} (hy : y ∈ (extChartAt (𝓡∂ 1) p).target) :
    (fderivWithin ℝ (fun z => ((extChartAt (𝓡∂ 1) p).symm z : ℝ))
      (extChartAt (𝓡∂ 1) p).target y).IsInvertible := by
  let c := extChartAt (𝓡∂ 1) p
  have hinc : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (Subtype.val : T.Point → ℝ) :=
    T.inclusion_smooth
  have hc := mdifferentiableWithinAt_extChartAt_symm (I := 𝓡∂ 1) hy
  have hu := (uniqueDiffOn_extChartAt_target (I := 𝓡∂ 1) p y hy).uniqueMDiffWithinAt
  have hm : mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ 1)
      c.symm c.target y =
      mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ 1)
        c.symm (range (𝓡∂ 1)) y :=
    hc.mfderivWithin_mono hu (extChartAt_target_subset_range p)
  rw [← mfderivWithin_eq_fderivWithin]
  change (mfderivWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ)
    ((Subtype.val : T.Point → ℝ) ∘ c.symm) c.target y).IsInvertible
  rw [mfderiv_comp_mfderivWithin y
    (hinc.mdifferentiable (by simp) (c.symm y))
    (hc.mono (extChartAt_target_subset_range p)) hu, hm,
    ← T.inclusionDerivative_eq]
  exact ContinuousLinearMap.isInvertible_equiv.comp
    (isInvertible_mfderivWithin_extChartAt_symm hy)

theorem realParam_smoothOn (T : SmoothSpacetimeInterval I) :
    ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ T.realParam I.domain := by
  intro t ht
  let p := T.realParam t
  let c := extChartAt (𝓡∂ 1) p
  let A := I.domain ∩ T.realParam ⁻¹' c.source
  have hp : T.realParam t ∈ c.source := mem_extChartAt_source p
  have htA : t ∈ A := ⟨ht, hp⟩
  have hinc : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (Subtype.val : T.Point → ℝ) :=
    T.inclusion_smooth
  have hc : ContDiffOn ℝ ∞ (fun z => (c.symm z : ℝ)) c.target := by
    exact (hinc.comp_contMDiffOn
      (contMDiffOn_extChartAt_symm p)).contDiffOn
  have hg : ContinuousOn (c ∘ T.realParam) A :=
    (continuousOn_extChartAt (I := 𝓡∂ 1) p).comp
      (T.realParam_continuousOn.mono inter_subset_left)
      (fun _ h => h.2)
  have hgs : MapsTo (c ∘ T.realParam) A c.target :=
    fun _ h => c.map_source h.2
  have hfg : ∀ y ∈ A, (c.symm (c (T.realParam y)) : ℝ) = y := by
    intro y hy
    rw [c.left_inv hy.2, T.realParam_val hy.1]
  have hi := contDiffOn_inverse_of_invertible_fderivWithin hc
    (uniqueDiffOn_extChartAt_target p) (fun y hy => chart_real_invertible T p hy)
    hg hgs hfg
  rw [contMDiffWithinAt_iff_target_of_mem_source (y := p)
    (by simpa only [c, extChartAt_source] using hp)]
  refine ⟨T.realParam_continuousOn t ht, ?_⟩
  apply (hi t htA).contMDiffWithinAt.mono_of_mem_nhdsWithin
  exact inter_mem self_mem_nhdsWithin
    ((T.realParam_continuousOn t ht) ((isOpen_extChartAt_source p).mem_nhds hp))

theorem realParam_mfderivWithin (T : SmoothSpacetimeInterval I)
    {t : ℝ} (ht : t ∈ I.domain) :
    mfderivWithin 𝓘(ℝ) (𝓡∂ 1) T.realParam I.domain t =
      (T.inclusionDerivative (T.realParam t)).symm.toContinuousLinearMap := by
  have hu := uniqueDiffWithinAt_of_spacetimeInterval I ⟨t, ht⟩
  have hinc : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (Subtype.val : T.Point → ℝ) :=
    T.inclusion_smooth
  have hcomp := mfderiv_comp_mfderivWithin t
    (hinc.mdifferentiable (by simp) (T.realParam t))
    (T.realParam_smoothOn.mdifferentiableOn (by simp) t ht) hu.uniqueMDiffWithinAt
  have hid : mfderivWithin 𝓘(ℝ) 𝓘(ℝ)
      ((Subtype.val : T.Point → ℝ) ∘ T.realParam) I.domain t =
      ContinuousLinearMap.id ℝ ℝ := by
    rw [mfderivWithin_eq_fderivWithin]
    exact ((hasFDerivWithinAt_id t I.domain).congr
      (fun s hs => T.realParam_val hs) (T.realParam_val ht)).fderivWithin hu
  rw [hid, ← T.inclusionDerivative_eq] at hcomp
  apply ContinuousLinearMap.ext
  intro a
  apply (T.inclusionDerivative (T.realParam t)).injective
  change (T.inclusionDerivative (T.realParam t))
    (mfderivWithin 𝓘(ℝ) (𝓡∂ 1) T.realParam I.domain t a) =
    (T.inclusionDerivative (T.realParam t)) ((T.inclusionDerivative (T.realParam t)).symm a)
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (congrArg (fun L : ℝ →L[ℝ] ℝ => L a) hcomp).symm

theorem realParam_mfderivWithin_one (T : SmoothSpacetimeInterval I) (t : T.Point) :
    mfderivWithin 𝓘(ℝ) (𝓡∂ 1) T.realParam I.domain t 1 = T.positiveTangent t := by
  rw [T.realParam_mfderivWithin t.property]
  change (T.inclusionDerivative (T.realParam t)).symm 1 = (T.inclusionDerivative t).symm 1
  rw [T.realParam_coe]

end

end PoincareConjecture.SmoothSpacetimeInterval

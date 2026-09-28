import PoincareConjecture.Proofs.M11.BoxGeometry
import PoincareConjecture.Proofs.M11.SpatialCalculus





set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M11

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

noncomputable def boxPositiveTangent (b : AdaptedMetricBox n X time I)
    (p : boxDomain b) : TangentSpace (spacetimeModel n) p :=
  ((smoothInterval b.interval).positiveTangent p.1, 0)

theorem box_time_smooth (b : AdaptedMetricBox n X time I) :
    ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ (fun q : boxDomain b ↦ q.1.val) := by
  let := intervalChartedSpace b.interval
  exact (smoothInterval b.interval).inclusion_smooth.comp contMDiff_fst

theorem box_space_smooth (b : AdaptedMetricBox n X time I) :
    ContMDiff (spacetimeModel n) (𝓡 n) ∞ (fun q : boxDomain b ↦ q.2.val) :=
  contMDiff_subtype_val.comp contMDiff_snd

theorem boxPositiveTangent_smooth (b : AdaptedMetricBox n X time I) :
    ContMDiff (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, SpacetimeModelVector n)) ∞
      (fun p : boxDomain b ↦ Bundle.TotalSpace.mk' (SpacetimeModelVector n)
        (E := (TangentSpace (spacetimeModel n) : boxDomain b → Type _)) p
        (boxPositiveTangent b p)) := by
  let := intervalChartedSpace b.interval
  let : IsManifold (𝓡∂ 1) ∞ b.interval.domain := interval_isManifold b.interval
  have ht : ContMDiff (spacetimeModel n)
      ((𝓡∂ 1).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))) ∞
      (fun p : boxDomain b ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin 1))
        (E := (TangentSpace (𝓡∂ 1) : (smoothInterval b.interval).Point → Type _))
        p.1 ((smoothInterval b.interval).positiveTangent p.1)) :=
    (smoothInterval b.interval).positive_tangent_smooth.comp contMDiff_fst
  have hx : ContMDiff (spacetimeModel n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : boxDomain b ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := (TangentSpace (𝓡 n) : b.spatial → Type _)) p.2 0) :=
    (Bundle.contMDiff_zeroSection ℝ (TangentSpace (𝓡 n) : b.spatial → Type _)).comp
      contMDiff_snd
  exact contMDiff_equivTangentBundleProd_symm.comp (ht.prodMk hx)

theorem box_time_mfderiv (b : AdaptedMetricBox n X time I) (p : boxDomain b)
    (v : TangentSpace (spacetimeModel n) p) :
    mfderiv (spacetimeModel n) 𝓘(ℝ) (fun q : boxDomain b ↦ q.1.val) p v =
      (smoothInterval b.interval).inclusionDerivative p.1 v.1 := by
  let := intervalChartedSpace b.interval
  change mfderiv (spacetimeModel n) 𝓘(ℝ)
    (Subtype.val ∘ (Prod.fst : boxDomain b → (smoothInterval b.interval).Point)) p v = _
  rw [mfderiv_comp_apply p
    (((smoothInterval b.interval).inclusion_smooth p.1).mdifferentiableAt (by simp))
    mdifferentiableAt_fst, mfderiv_fst]
  rfl

theorem boxPositiveTangent_normalized (b : AdaptedMetricBox n X time I) (p : boxDomain b) :
    mfderiv (spacetimeModel n) 𝓘(ℝ) (fun q : boxDomain b ↦ q.1.val) p
      (boxPositiveTangent b p) = 1 := by
  rw [box_time_mfderiv]
  exact ((smoothInterval b.interval).inclusionDerivative p.1).apply_symm_apply 1

theorem box_space_mfderiv (b : AdaptedMetricBox n X time I) (p : boxDomain b)
    (v : TangentSpace (spacetimeModel n) p) :
    mfderiv (spacetimeModel n) (𝓡 n) (fun q : boxDomain b ↦ q.2.val) p v = v.2 := by
  change mfderiv (spacetimeModel n) (𝓡 n)
    (Subtype.val ∘ (Prod.snd : boxDomain b → b.spatial)) p v = _
  rw [mfderiv_comp_apply p
    (contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp))
    mdifferentiableAt_snd, mfderiv_snd, mfderiv_openSubtype_val]
  rfl

end PoincareConjecture.Proofs.M11

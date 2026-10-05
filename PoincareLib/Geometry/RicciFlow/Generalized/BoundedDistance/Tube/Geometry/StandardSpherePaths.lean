import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.RoundCylinder
import PoincareLib.Geometry.Riemannian.Normalization.Metric.Construction
import PoincareLib.Geometry.Riemannian.Metric.Gluing.InducedForm
import PoincareLib.Geometry.Riemannian.ScalarOperators.Euclidean
import PoincareLib.Geometry.Riemannian.Distance.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Order.Compact

/-!
# A fixed path ceiling on the literal unit sphere

Morgan--Tian Appendix A.1, pp. 497-498, uses uniformly short paths on
central spheres. The induced Euclidean metric on the actual unit sphere
is constructed here. Compactness and finite Riemannian distance give one
finite C1 path ceiling, selected before every neck or ambient flow.
The later shortening argument can shrink epsilon using this fixed ceiling;
no sharp diameter formula is needed.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle InnerProductSpace

namespace PoincareMT.M28

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private theorem standardSphereInner_pos (q : UnitTwoSphere)
    (v : TangentSpace (𝓡 2) q) (hv : v ≠ 0) :
    0 < Poincare.Gluing.inducedForm (I := 𝓡 2) (J := 𝓡 3)
      (RiemannianMetric.euclideanMetric 3) (fun x : UnitTwoSphere => x.1) q v v := by
  change 0 < inner ℝ
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q v)
    (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q v)
  apply real_inner_self_pos.mpr
  intro hzero
  apply hv
  have hinj : Function.Injective
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q) := by
    convert! injective_mvfderiv_subtypeVal_sphere q using 1
  apply hinj
  simpa only [map_zero] using hzero

/-- The actual unit-sphere metric, induced by its Euclidean inclusion. -/
noncomputable def standardSphereMetric : RiemannianMetric 2 UnitTwoSphere where
  inner := Poincare.Gluing.inducedForm (I := 𝓡 2) (J := 𝓡 3)
    (RiemannianMetric.euclideanMetric 3) (fun x : UnitTwoSphere => x.1)
  symm q v w := by
    change inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q v)
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q w) = inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q w)
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q v)
    exact real_inner_comm _ _
  pos := standardSphereInner_pos
  isVonNBounded q := by
    change Bornology.IsVonNBounded ℝ {v : EuclideanSpace ℝ (Fin 2) |
      Poincare.Gluing.inducedForm (I := 𝓡 2) (J := 𝓡 3)
        (RiemannianMetric.euclideanMetric 3) (fun x : UnitTwoSphere => x.1) q v v < 1}
    exact m01_isVonNBounded_of_posDef _ (standardSphereInner_pos q)
  contMDiff q := Poincare.Gluing.inducedForm_contMDiffAt
    (RiemannianMetric.euclideanMetric 3) (contMDiff_coe_sphere q)

/-- The constructed metric is the literal pullback of the Euclidean form. -/
@[simp] theorem standardSphereMetric_inner (q : UnitTwoSphere)
    (v w : TangentSpace (𝓡 2) q) :
    standardSphereMetric.inner q v w = inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q v)
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q w) := rfl

/-- Its speed is the Euclidean speed of the actual sphere inclusion. -/
theorem standardSphereMetric_tangentNorm (q : UnitTwoSphere)
    (v : TangentSpace (𝓡 2) q) :
    standardSphereMetric.tangentNorm q v =
      ‖mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) q v‖ := by
  simp only [RiemannianMetric.tangentNorm, standardSphereMetric_inner,
    real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- Compactness of the one fixed standard sphere produces an actual
uniform finite ceiling for C1 paths with flat endpoints (Appendix A.1). -/
theorem exists_standardSphere_path_ceiling :
    ∃ L : ℝ, 0 < L ∧ ∀ p q : UnitTwoSphere, ∃ γ : ℝ → UnitTwoSphere,
      γ 0 = p ∧ γ 1 = q ∧ ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 γ ∧
      standardSphereMetric.pathELength γ 0 1 < ENNReal.ofReal L ∧
      γ =ᶠ[𝓝 (0 : ℝ)] (fun _ => p) ∧ γ =ᶠ[𝓝 (1 : ℝ)] (fun _ => q) := by
  have hs : IsConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) _ (by norm_num)
  let : ConnectedSpace UnitTwoSphere := Subtype.connectedSpace hs
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 2) : UnitTwoSphere → Type _) :=
    ⟨standardSphereMetric.toRiemannianMetric⟩
  obtain ⟨o, ho⟩ := hs.nonempty
  let p₀ : UnitTwoSphere := ⟨o, ho⟩
  obtain ⟨r, _, hr⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (univ : Set UnitTwoSphere).Nonempty)
    (standardSphereMetric.continuous_toReal_edist p₀).continuousOn
  let B : ℝ := (standardSphereMetric.edist p₀ r).toReal
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  refine ⟨2 * B + 1, by positivity, ?_⟩
  intro p q
  have hp : (standardSphereMetric.edist p p₀).toReal ≤ B := by
    have heq : standardSphereMetric.edist p p₀ = standardSphereMetric.edist p₀ p :=
      Manifold.riemannianEDist_comm
    rw [heq]
    exact hr (mem_univ p)
  have hq : (standardSphereMetric.edist p₀ q).toReal ≤ B := hr (mem_univ q)
  have hdist : standardSphereMetric.edist p q < ENNReal.ofReal (2 * B + 1) := by
    apply (ENNReal.toReal_lt_toReal (standardSphereMetric.edist_ne_top p q)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    have htriangle := standardSphereMetric.toReal_edist_triangle p p₀ q
    linarith
  exact Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hdist zero_lt_one

/-- This constant depends only on the literal standard sphere. -/
noncomputable def standardSpherePathCeiling : ℝ :=
  Classical.choose exists_standardSphere_path_ceiling

/-- The fixed standard-sphere path ceiling is strictly positive. -/
theorem standardSpherePathCeiling_pos : 0 < standardSpherePathCeiling :=
  (Classical.choose_spec exists_standardSphere_path_ceiling).1

/-- Actual sphere paths under the fixed ceiling; no ambient manifold or
neck is supplied before the ceiling is chosen. -/
theorem exists_standardSphere_short_path (p q : UnitTwoSphere) :
    ∃ γ : ℝ → UnitTwoSphere, γ 0 = p ∧ γ 1 = q ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) 1 γ ∧
      standardSphereMetric.pathELength γ 0 1 < ENNReal.ofReal standardSpherePathCeiling ∧
      γ =ᶠ[𝓝 (0 : ℝ)] (fun _ => p) ∧ γ =ᶠ[𝓝 (1 : ℝ)] (fun _ => q) :=
  (Classical.choose_spec exists_standardSphere_path_ceiling).2 p q

end PoincareMT.M28

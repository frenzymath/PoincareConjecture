import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.Manifold.OpenSubsetShift

/-!
# Actual derivatives of shifted spatial curves

Morgan-Tian Lemma 6.4, pp. 107-108. On its admissible open domain,
the included affine shift has exactly the derivative of the affine
coordinate expression. Its subtype-valued curve retains C1 regularity.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace TopologicalSpace.Opens

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Opens E)
  (u : ℝ → U) (η : ℝ → E) {s v : ℝ}

/-- An admissible affine shift of a C1 spatial curve remains C1 near
the selected point, the variation construction of Lemma 6.4,
pp. 107-108. -/
theorem affineShift_curve_contMDiffAt
    (hu : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 u s)
    (hη : ContDiffAt ℝ 1 η s) (hshift : (u s).val + v • η s ∈ U) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 (fun t => U.affineShift (u t) (v • η t)) s := by
  have hηv : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) 1 (fun t => v • η t) s :=
    ((contDiffAt_const (c := v)).smul hη).contMDiffAt
  exact (((U.affineShift_contMDiffOn _ hshift).contMDiffAt
    (U.affineShift_domain_isOpen.mem_nhds hshift)).of_le (by simp)).comp s (hu.prodMk hηv)

/-- The actual ambient derivative of an admissible affine spatial
shift is the original derivative plus the shifted test derivative,
Lemma 6.4, pp. 107-108. -/
theorem affineShift_curve_hasDerivAt
    (hu : DifferentiableAt ℝ (fun t => (u t).val) s)
    (hη : DifferentiableAt ℝ η s) (hshift : (u s).val + v • η s ∈ U) :
    HasDerivAt (fun t => (U.affineShift (u t) (v • η t)).val)
      (deriv (fun t => (u t).val) s + v • deriv η s) s := by
  have hcont := hu.continuousAt.add (hη.continuousAt.const_smul v)
  apply (hu.hasDerivAt.add (hη.hasDerivAt.const_smul v)).congr_of_eventuallyEq
  filter_upwards [hcont.preimage_mem_nhds (U.isOpen.mem_nhds hshift)] with t ht
  exact U.affineShift_val ht

end TopologicalSpace.Opens

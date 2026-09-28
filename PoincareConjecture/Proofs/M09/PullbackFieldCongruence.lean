import PoincareConjecture.Proofs.M09.PullbackExtension








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem pullbackCovariantDerivative_field_congr {J : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) (α : ℝ → M)
    (Y Z : ∀ t, TangentSpace (𝓡 n) (α t)) (I : Set ℝ)
    (HY : ParametricAlongCurveExtensionOn (n := n) I α Y)
    (HZ : ParametricAlongCurveExtensionOn (n := n) I α Z)
    (hYZ : ∀ t ∈ I, Y t = Z t) (s : ℝ) (hs : s ∈ I)
    (hI : UniqueDiffWithinAt ℝ I s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y I HY s =
      pullbackCovariantDerivative F time α Z I HZ s := by
  let H : ParametricAlongCurveExtensionOn (n := n) I α Y := {
    extension := HZ.extension
    domain := HZ.domain
    open_domain := HZ.open_domain
    graph_mem := HZ.graph_mem
    smooth := HZ.smooth
    agrees := fun t ht ↦ (HZ.agrees t ht).trans (hYZ t ht).symm
  }
  exact pullbackCovariantDerivative_extension_independent F time α Y I HY H s hs hI hα

theorem pullbackCovariantDerivative_curve_field_congr {J : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) (α β : ℝ → M)
    (Y : ∀ t, TangentSpace (𝓡 n) (α t))
    (Z : ∀ t, TangentSpace (𝓡 n) (β t)) (I : Set ℝ)
    (HY : ParametricAlongCurveExtensionOn (n := n) I α Y)
    (HZ : ParametricAlongCurveExtensionOn (n := n) I β Z)
    (hαβ : α = β) (hYZ : ∀ t ∈ I, (Y t : E) = Z t)
    (s : ℝ) (hs : s ∈ I) (hI : UniqueDiffWithinAt ℝ I s)
    (hβ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) β s) :
    (pullbackCovariantDerivative F time α Y I HY s : E) =
      pullbackCovariantDerivative F time β Z I HZ s := by
  subst β
  exact pullbackCovariantDerivative_field_congr F time α Y Z I HY HZ hYZ s hs hI hβ

end PoincareConjecture.Proofs.M09

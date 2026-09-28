import PoincareConjecture.Proofs.M09.LocalRegularizedEquation
import PoincareConjecture.Proofs.M09.CompactVelocityExtension








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_regularizedExtensionOn_compact {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (γ : ℝ → M)
    (U K : Set ℝ) (hU : IsOpen U) (hKU : K ⊆ U) (hK : IsCompact K)
    (hKd : UniqueDiffOn ℝ K) (htime : K ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ U)
    (heq : ∀ s ∈ K, LocalRegularizedEquation F T γ s) :
    ∃ E : ParametricAlongCurveExtensionOn (n := n) K γ (curveVelocityWithin (n := n) γ K),
      ∀ s ∈ K, regularizedLGeodesicEquation F T γ K E s := by
  obtain ⟨E⟩ := nonempty_velocityExtensionOn_compact γ U K hU hKU hK hKd hγ
  exact ⟨E, fun s hs ↦ (regularizedEquation_iff_local F hM04 T b hb hwindow γ
    U K hU hKU hKd hγ E s hs (htime hs)).mpr (heq s hs)⟩

end PoincareConjecture.Proofs.M09

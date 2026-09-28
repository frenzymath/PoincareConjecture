import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPolarDescent
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerAnnularCap













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem scalarAreaDensity_comp_localDiffeomorph
    (g : RiemannianMetric n M) (f : Plane → M) {k : Plane → Plane} {p : Plane}
    (hk : ContDiffAt ℝ 1 k p) (hkinv : (fderiv ℝ k p).IsInvertible) :
    m60AreaDensity g (f ∘ k) p =
      |(fderiv ℝ k p).det| * m60AreaDensity g f (k p) := by
  by_cases hf : MDifferentiableAt (𝓡 2) (𝓡 n) f (k p)
  · exact M60.suAreaDensity_comp_plane g hf (hk.differentiableAt one_ne_zero)
  · obtain ⟨A, hA⟩ := hkinv
    have hstrict : HasStrictFDerivAt k (A : Plane →L[ℝ] Plane) p := by
      rw [hA]
      exact hk.hasStrictFDerivAt one_ne_zero
    let q := hstrict.localInverse k A p
    have hcomp : ¬MDifferentiableAt (𝓡 2) (𝓡 n) (f ∘ k) p := by
      intro h
      have hback := h.comp_of_eq (k p)
        hstrict.to_localInverse.hasFDerivAt.hasMFDerivAt.mdifferentiableAt
        hstrict.localInverse_apply_image
      have heq : (f ∘ k) ∘ q =ᶠ[𝓝 (k p)] f :=
        hstrict.eventually_right_inverse.mono (fun x hx => congrArg f hx)
      exact hf (heq.mdifferentiableAt_iff.mp hback)
    have hzero {h : Plane → M} {z : Plane}
        (hh : ¬MDifferentiableAt (𝓡 2) (𝓡 n) h z) : m60AreaDensity g h z = 0 := by
      have hgram : m60AreaGram g h z = 0 := by
        ext i j
        simp only [m60AreaGram, mfderiv_zero_of_not_mdifferentiableAt hh]
        change g.inner (h z) 0 0 = 0
        simp
      simp [m60AreaDensity, hgram]
    rw [hzero hf, hzero hcomp, mul_zero]

end PoincareConjecture.M64Uniformization

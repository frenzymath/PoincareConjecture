import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereCollarCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereNormalSign
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FixedSphereBallPreservation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem exists_oriented_collar_extension (e : OpenPartialHomeomorph E E)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    (hsource : sphere (0 : E) 1 ⊆ e.source)
    (hfixed : ∀ x ∈ sphere (0 : E) 1, e x = x)
    (hout : ∀ x ∈ sphere (0 : E) 1,
      ∀ᶠ y in 𝓝 x, 1 ≤ ‖y‖ → 1 ≤ ‖e y‖) :
    ∃ F : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      (∀ x ∈ sphere (0 : E) 1, F x = x) ∧
      (∀ᶠ x in 𝓝ˢ (sphere (0 : E) 1), F x = e x) ∧
      F '' ball (0 : E) 1 = ball 0 1 ∧
      F '' closedBall (0 : E) 1 = closedBall 0 1 ∧
      ∃ C : Set E, IsCompact C ∧ ∀ x, x ∉ C → F x = x := by
  have hn (x : E) (hx : x ∈ sphere (0 : E) 1) :
      0 < inner ℝ x (fderiv ℝ e x x) := by
    obtain ⟨A, hA⟩ := exists_smoothChart_derivative e he hi (hsource hx)
    apply fderiv_normal_pos_of_local_exterior e (mem_sphere_zero_iff_norm.mp hx)
      hA.differentiableAt
      (Filter.Eventually.of_forall fun y hy => hfixed y (mem_sphere_zero_iff_norm.mpr hy))
      (by rw [hA.fderiv]; exact A.injective) (hout x hx)
  obtain ⟨Φ, hΦ, hzero, hfix, hnear, C, hC, hsupport⟩ :=
    exists_sphere_collar_correction e e.open_source hsource he hfixed hn
  have hballs := fixedSphere_isotopy_image_balls (fun t => (Φ t).toHomeomorph)
    (fun x => (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn)
    hzero (fun t ht x hx => hfix t ht x (mem_sphere_zero_iff_norm.mpr hx))
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  exact ⟨Φ 1, hfix 1 (by norm_num), hnear, hballs.1, hballs.2,
    C, hC, hsupport 1⟩

end PoincareConjecture.M25.Topology3D

import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereInterpolation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyExtension












set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]




theorem exists_sphere_collar_correction (f : E → E) {U : Set E}
    (hU : IsOpen U) (hSU : sphere (0 : E) 1 ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hfixed : ∀ x ∈ sphere (0 : E) 1, f x = x)
    (hn : ∀ x ∈ sphere (0 : E) 1, 0 < ⟪x, fderiv ℝ f x x⟫_ℝ) :
    ∃ Φ : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      ContDiff ℝ ∞ (fun p : ℝ × E => Φ p.1 p.2) ∧
      (∀ x, Φ 0 x = x) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ sphere (0 : E) 1, Φ t x = x) ∧
      (∀ᶠ x in 𝓝ˢ (sphere (0 : E) 1), Φ 1 x = f x) ∧
      ∃ C : Set E, IsCompact C ∧ ∀ t x, x ∉ C → Φ t x = x := by
  obtain ⟨e, heq, hsource, _, he, hi⟩ :=
    exists_sphereInterpolation_chart f hU hSU hf hfixed hn (-1) 2
  obtain ⟨V, W, _, hW, hIV, hSW, hVW⟩ := generalized_tube_lemma
    isCompact_Icc (isCompact_sphere (0 : E) 1) e.open_source hsource
  obtain ⟨S, hS, hSS, hSW'⟩ := exists_compact_between (isCompact_sphere (0 : E) 1) hW hSW
  have hIS : Icc (-1 : ℝ) 2 ×ˢ S ⊆ e.source :=
    fun _ hp => hVW ⟨hIV hp.1, hSW' hp.2⟩
  have htime (p : ℝ × E) (_hp : p ∈ e.source) : (e p).1 = p.1 := by
    rw [heq]
    rfl
  have hlinear (p : ℝ × E) (_hp : p ∈ e.source) :
      (0 : E →L[ℝ] ℝ) (e p).2 = (0 : E →L[ℝ] ℝ) p.2 := rfl
  obtain ⟨Φ, hΦ, hzero, htracks, ⟨C, hC, _, hsupport⟩, _⟩ :=
    exists_ambient_isotopy_of_chart e he hi htime (0 : E →L[ℝ] ℝ) hlinear hS
      (show (0 : ℝ) ∈ Ioo (-1) 2 by norm_num) hIS
  have hagree (x : E) (hx : x ∈ S) (t : ℝ) (ht : t ∈ Ioo (-1) 2) :
      Φ t x = (sphereInterpolation f (t, x)).2 := by
    have h := htracks x hx t ht
    rw [heq, sphereInterpolation_zero] at h
    exact h
  refine ⟨Φ, hΦ, hzero, ?_, ?_, C, hC, hsupport⟩
  · intro t ht x hx
    rw [hagree x (interior_subset (hSS hx)) t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      sphereInterpolation_fixed f t (hfixed x hx)]
  · apply eventually_nhdsSet_iff_forall.mpr
    intro x hx
    filter_upwards [isOpen_interior.mem_nhds (hSS hx)] with y hy
    rw [hagree y (interior_subset hy) 1 (by norm_num), sphereInterpolation_one]

end PoincareConjecture.M25.Topology3D

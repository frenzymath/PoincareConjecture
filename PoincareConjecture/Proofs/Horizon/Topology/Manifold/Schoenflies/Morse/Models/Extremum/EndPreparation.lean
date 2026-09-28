import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.NormalForm
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.CylinderEnd
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Caps

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_minimum_preparation_with_profile
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hmin : IsLocalMin (fun q => inner Real v (f q)) p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 → Real) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) + ∑ i : Fin 2, σ i * x i ^ 2)
    {η : Real} (hη : 0 < η) :
    ∃ J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v, ∃ r ∈ Ioo (0 : Real) η,
      closedBall (0 : E2) r ⊆ e.source ∧
      ∃ A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        (∀ (t : Real) (x : Hemisphere.Plane v),
          inner Real v (f p) + 3 * r ^ 2 / 2 ≤ t →
          D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        (∀ x ∈ closedBall (0 : E2) r,
          D (f (e x)) =
            ((Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • J x : Hemisphere.Plane v) +
              (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        (∀ x ∈ closedBall (0 : E2) (r / 2),
          D (f (e x)) = (J x : E3) + (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        ∀ (q : E2) (ρ : Real), ‖q‖ = 1 → ρ ∈ Icc (3 * r / 4) r →
          D (f (e (ρ • q))) =
            (r • J q : Hemisphere.Plane v) + (inner Real v (f p) + ρ ^ 2) • v := by
  have hsign : ∀ i, σ i = 1 := morse_signs_eq_one_of_isLocalMin
    (h := fun q => inner Real v (f q)) e he0 σ hσ
    (by simpa only [hep] using hform) (by simpa only [hep] using hmin)
  have hsum (x : E2) : (∑ i : Fin 2, σ i * x i ^ 2) = ‖x‖ ^ 2 := by
    simp only [hsign, one_mul, ← EuclideanSpace.real_norm_sq_eq]
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q => inner Real v (f q)) :=
    (innerSL Real v).contMDiff.comp hf.contMDiff
  have hp := Poincare.Geometry.Manifold.mfderiv_eq_zero_of_isLocalMin hh hmin
  obtain ⟨J, R, hR, hRs, A, H, hHheight, hHplane, hH⟩ :=
    exists_height_preserving_critical_graph_with_plane_action hf hv p hp e he0 hep he hei σ hform
  let r : Real := min R η / 2
  have hr : 0 < r := half_pos (lt_min hR hη)
  have hrR : r ≤ R := by dsimp [r]; linarith [min_le_left R η]
  have hrη : r < η := by dsimp [r]; linarith [min_le_right R η]
  obtain ⟨G, hGheight, hGlow, hGhigh, hGprofile, hGcylinder⟩ :=
    exists_quadratic_minimum_cylindrical_end_with_profile hv (inner Real v (f p)) hr
  let D := H.trans G
  refine ⟨J, r, ⟨hr, hrη⟩, (closedBall_subset_closedBall hrR).trans hRs,
    A, D, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact (hGheight (H y)).trans (hHheight y)
  · intro t x ht
    change G (H (t • v + (x : E3))) = _
    rw [hHplane]
    apply hGhigh
    simpa only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hv,
      one_pow, mul_one,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (A x).property, add_zero] using ht
  · intro x hx
    change G (H (f (e x))) = _
    rw [hH x (closedBall_subset_closedBall hrR hx), hsum]
    simpa only [J.norm_map] using hGprofile (J x)
      (by simpa only [J.norm_map] using mem_closedBall_zero_iff.mp hx)
  · intro x hx
    have hxr : x ∈ closedBall (0 : E2) R :=
      closedBall_subset_closedBall (by linarith : r / 2 ≤ R) hx
    change G (H (f (e x))) = _
    rw [hH x hxr, hsum]
    apply hGlow
    have hxnorm := mem_closedBall_zero_iff.mp hx
    have hJ : inner Real v (J x : E3) = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp (J x).property
    simp only [inner_add_right, inner_smul_right, hJ, real_inner_self_eq_norm_sq, hv,
      one_pow, mul_one, zero_add]
    nlinarith [norm_nonneg x]
  · intro q ρ hq hρ
    have hρpos : 0 < ρ := by linarith [hρ.1]
    have hnorm : ‖ρ • q‖ = ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos, hq, mul_one]
    have hqr : ρ • q ∈ closedBall (0 : E2) R :=
      mem_closedBall_zero_iff.mpr (by rw [hnorm]; exact hρ.2.trans hrR)
    change G (H (f (e (ρ • q)))) = _
    rw [hH _ hqr, hsum, hnorm, J.map_smul]
    exact hGcylinder (J q) ρ (by simpa using hq) hρpos
      (by nlinarith [hρ.1]) ((sq_le_sq₀ hρpos.le hr.le).mpr hρ.2)

theorem exists_minimum_preparation_with_upper_plane_action
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (p : S2)
    (hmin : IsLocalMin (fun q => inner Real v (f q)) p)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 → Real) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) =
      inner Real v (f p) + ∑ i : Fin 2, σ i * x i ^ 2)
    {η : Real} (hη : 0 < η) :
    ∃ J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v, ∃ r ∈ Ioo (0 : Real) η,
      closedBall (0 : E2) r ⊆ e.source ∧
      ∃ A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
          (Hemisphere.Plane v) (Hemisphere.Plane v) ∞,
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y, inner Real v (D y) = inner Real v y) ∧
        (∀ (t : Real) (x : Hemisphere.Plane v),
          inner Real v (f p) + 3 * r ^ 2 / 2 ≤ t →
          D (t • v + (x : E3)) = t • v + (A x : E3)) ∧
        (∀ x ∈ closedBall (0 : E2) (r / 2),
          D (f (e x)) = (J x : E3) + (inner Real v (f p) + ‖x‖ ^ 2) • v) ∧
        ∀ (q : E2) (ρ : Real), ‖q‖ = 1 → ρ ∈ Icc (3 * r / 4) r →
          D (f (e (ρ • q))) =
            (r • J q : Hemisphere.Plane v) + (inner Real v (f p) + ρ ^ 2) • v := by
  obtain ⟨J, r, hr, hrs, A, D, hheight, hupper, _, hcenter, hcylinder⟩ :=
    exists_minimum_preparation_with_profile hf hv p hmin e he0 hep he hei σ hσ hform hη
  exact ⟨J, r, hr, hrs, A, D, hheight, hupper, hcenter, hcylinder⟩

end Poincare.Manifold.Schoenflies

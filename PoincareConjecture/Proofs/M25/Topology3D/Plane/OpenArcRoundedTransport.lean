import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcRoundingProducer
import PoincareConjecture.Proofs.M25.Topology3D.Plane.OpenArcTubeHomotopy

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_openArc_rounded_tube_transport
    {ρ : ℝ → ℝ} {P : (ℝ × ℝ) → ℤ → (ℝ × ℝ)}
    (data : OpenArcRoundedData ρ P)
    (hglobal : ∀ z, Injective (fun u : ℝ => openArcRoundedFamily ρ P z u))
    (hstationary : ∀ t s, t ≤ 0 ∨ 1 ≤ t → ∀ i : ℤ, P (t, s) i = P (t, 0) i)
    (haxis : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ℝ,
      (openArcRoundedFamily ρ P (t, 1) u).2 = 0) :
    ∃ G : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (G p.1).symm p.2) ∧
      (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ t x, x ∉ Q → G t x = x ∧ (G t).symm x = x) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, G t x = x ∧ (G t).symm x = x) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u : ℝ,
        (G t (openArcRoundedFamily ρ P (t, 0) u)).2 = 0 := by
  let D : (ℝ × ℝ) × ℝ → ℝ × ℝ :=
    fun p => openArcRoundedFamily ρ P p.1 p.2
  have hD : ContDiff ℝ ∞ D := by
    simpa only [D] using contDiff_openArcRoundedFamily data
  have hDinj : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1,
      Injective (fun u : ℝ => D (z, u)) := by
    intro z _
    simpa only [D] using hglobal z
  have hDreg : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, ∀ u : ℝ,
      fderiv ℝ (fun v : ℝ => D (z, v)) u 1 ≠ 0 := by
    intro z _ u
    simpa only [D] using openArcRoundedFamily_fderiv_regular data z u
  let R : ℝ := data.tail_radius + 4
  have hR : 0 < R := by
    dsimp [R]
    linarith [data.tail_radius_pos]
  have hDtail : ∀ z u, R ≤ |u| → D (z, u) = (u, 0) := by
    intro z u hu
    exact openArcRoundedFamily_axis_tail data z u (by simpa [R] using hu)
  have hDstat : ∀ t s u, t ≤ 0 ∨ 1 ≤ t → D ((t, s), u) = D ((t, 0), u) := by
    intro t s u ht
    simp only [D, openArcRoundedFamily]
    congr 1
    funext i
    exact hstationary t s ht i
  exact exists_openArc_tube_homotopy_transport D hR hD hDinj hDreg hDtail hDstat haxis

end PoincareConjecture.M25.Topology3D

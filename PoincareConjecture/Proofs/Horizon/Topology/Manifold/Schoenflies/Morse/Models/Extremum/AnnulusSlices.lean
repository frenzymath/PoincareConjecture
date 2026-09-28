import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.BandCoverage

noncomputable section
set_option autoImplicit false

open Set Metric Function

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem annular_slice_eq_level_of_full_band
    {h : S2 → Real} {a b δ : Real} (hδ : 0 < δ)
    (F : OpenPartialHomeomorph (S1 × Real) S2)
    (hheight : ∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t)
    (hband : F '' (univ ×ˢ Icc a b) = h ⁻¹' Icc a b)
    {t : Real} (ht : t ∈ Icc a b) :
    range (fun q : S1 => F (q, t)) = h ⁻¹' {t} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact hheight q t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro hx
    change h x = t at hx
    have hxband : x ∈ h ⁻¹' Icc a b := by rw [mem_preimage, hx]; exact ht
    rw [← hband] at hxband
    obtain ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩ := hxband
    have hsheight := hheight q s ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hst : s = t := hsheight.symm.trans hx
    exact ⟨q, by rw [hst]⟩

theorem image_unit_sphere_smul {r : Real} (hr : 0 < r) :
    range (fun q : S1 => r • (q : E2)) = sphere (0 : E2) r := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simp
  · intro hx
    have hxnorm := mem_sphere_zero_iff_norm.mp hx
    have hq : ‖r⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), hxnorm,
        inv_mul_cancel₀ hr.ne']
    refine ⟨⟨r⁻¹ • x, mem_sphere_zero_iff_norm.mpr hq⟩, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

end Poincare.Manifold.Schoenflies

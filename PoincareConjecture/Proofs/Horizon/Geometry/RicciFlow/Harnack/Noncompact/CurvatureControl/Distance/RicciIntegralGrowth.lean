import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.RicciIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Distance.RicciIntegralMoments


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

theorem integral_ricci_le_of_quadratic_endpoint_bounds
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {γ : ℝ → M} {I : Set ℝ} {L A B scale c : ℝ}
    (hI : IsOpen I) (hsub : Icc 0 L ⊆ I)
    (hgeo : g.IsGeodesicOn γ I) (hL : 0 ≤ L) (hc : 0 < c)
    (hspeed : ∀ s ∈ Icc 0 L, g.tangentNorm (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = c)
    (hmin : g.edist (γ 0) (γ L) = ENNReal.ofReal (L * c))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hscale : 0 < scale)
    (hleft : ∀ s ∈ Icc 0 L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ A + B * s ^ 2)
    (hright : ∀ s ∈ Icc 0 L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ A + B * (L - s) ^ 2) :
    (∫ s in (0 : ℝ)..L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)) ≤
      2 * (n : ℝ) * scale + 4 * A / scale + 8 * B / scale ^ 3 := by
  have h := D.integral_ricci_le_of_constant_speed_weighted_upper hI hsub hgeo hL hc
    hspeed hmin (Λ := fun s => min (A + B * s ^ 2) (A + B * (L - s) ^ 2))
    (by fun_prop) hscale (fun s hs => le_min (hleft s hs) (hright s hs))
  have hmoment := Poincare.RicciIntegral.integral_cutoff_defect_min_quadratic_le
    hL hscale hA hB
  linarith

theorem integral_ricci_div_speed_le_of_quadratic_endpoint_bounds
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {γ : ℝ → M} {I : Set ℝ} {L A B scale c : ℝ}
    (hI : IsOpen I) (hsub : Icc 0 L ⊆ I)
    (hgeo : g.IsGeodesicOn γ I) (hL : 0 ≤ L) (hc : 0 < c)
    (hspeed : ∀ s ∈ Icc 0 L, g.tangentNorm (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) = c)
    (hmin : g.edist (γ 0) (γ L) = ENNReal.ofReal (L * c))
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hscale : 0 < scale)
    (hleft : ∀ s ∈ Icc 0 L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ (A + B * (s * c) ^ 2) * c ^ 2)
    (hright : ∀ s ∈ Icc 0 L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) ≤ (A + B * ((L - s) * c) ^ 2) * c ^ 2) :
    (∫ s in (0 : ℝ)..L, D.ricci (γ s)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ s 1) / c) ≤
      2 * (n : ℝ) * scale + 4 * A / scale + 8 * B / scale ^ 3 := by
  have h := D.integral_ricci_le_of_quadratic_endpoint_bounds hI hsub hgeo hL hc hspeed hmin
    (A := A * c ^ 2) (B := B * c ^ 4) (scale := scale * c)
    (by positivity) (by positivity) (mul_pos hscale hc)
    (fun s hs => (hleft s hs).trans_eq (by ring))
    (fun s hs => (hright s hs).trans_eq (by ring))
  rw [intervalIntegral.integral_div]
  apply (div_le_iff₀ hc).mpr
  apply h.trans_eq
  field_simp

end PoincareConjecture.LeviCivitaData

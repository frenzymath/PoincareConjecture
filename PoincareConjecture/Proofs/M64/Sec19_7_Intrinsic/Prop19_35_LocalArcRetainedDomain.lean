import PoincareConjecture.Proofs.M64.Mathlib.ShiftedWeightedFocusingCover
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingLoss

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Matrix

namespace PoincareConjecture

theorem m64Intrinsic_exists_local_arc_retained_normal_domain
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (height : ℝ → ℝ) {l u : ℝ} (hlu : l < u)
    {X : Set ℝ} (hX : X ⊆ Ioo l u)
    {A τ : ℝ} (hA : 0 ≤ A) (hτ : 3 < τ)
    (hray : ∀ a ∈ X, InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)))
    (hfocus : ∀ a ∈ X, ∀ b ∈ X, a < b →
      (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b), e !₂[a, t] = e !₂[b, s]) →
      intrinsicBoundaryLength N.metric 1 a b ≤
        A * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc l u ∧
      (∫ x in E, intrinsicBoundarySpeed N.metric 1 x) ≤
        (τ * A) * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 l u ∧
      InjOn e {z : AnnulusCoordinates | z 0 ∈ X \ E ∧ z 1 ∈ Icc 0 (height (z 0))} := by
  let T : Set (ℝ × ℝ) := {p | p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 < p.2 ∧
    ∃ t ∈ Icc 0 (height p.1), ∃ s ∈ Icc 0 (height p.2), e !₂[p.1, t] = e !₂[p.2, s]}
  have hT (p : ℝ × ℝ) (hp : p ∈ T) :
      l ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ u :=
    ⟨(hX hp.1).1.le, hp.2.2.1, (hX hp.2.1).2.le⟩
  obtain ⟨E, hE, hEsub, hcover, hbound⟩ :=
    m64_exists_shifted_weighted_focusing_cover
      (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
      (m64Intrinsic_boundarySpeed_pos N (by norm_num : (1 : ℝ) ≠ 0))
      (m64Intrinsic_continuous_turning_density N (by norm_num : (1 : ℝ) ≠ 0))
      (fun _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      hlu hA hτ T hT (fun p hp => hfocus p.1 hp.1 p.2 hp.2.1 hp.2.2.1 hp.2.2.2)
  refine ⟨E, hE, hEsub, hbound, ?_⟩
  have hrepr (z : AnnulusCoordinates) : !₂[z 0, z 1] = z := by
    ext i
    fin_cases i <;> rfl
  intro x hx y hy hxy
  have heq : x 0 = y 0 := by
    rcases lt_trichotomy (x 0) (y 0) with hlt | heq | hlt
    · have hpair : (x 0, y 0) ∈ T :=
        ⟨hx.1.1, hy.1.1, hlt, x 1, hx.2, y 1, hy.2, by simpa only [hrepr] using hxy⟩
      exact False.elim (hx.1.2 (hcover _ hpair ⟨le_rfl, hlt.le⟩))
    · exact heq
    · have hpair : (y 0, x 0) ∈ T :=
        ⟨hy.1.1, hx.1.1, hlt, y 1, hy.2, x 1, hx.2, by simpa only [hrepr] using hxy.symm⟩
      exact False.elim (hy.1.2 (hcover _ hpair ⟨le_rfl, hlt.le⟩))
  have hyrepr : !₂[x 0, y 1] = y := by rw [heq, hrepr]
  have ht : x 1 = y 1 := hray (x 0) hx.1.1 hx.2
    (by simpa only [heq] using hy.2) (by simpa only [hrepr, hyrepr] using hxy)
  ext i
  fin_cases i
  · exact heq
  · exact ht

theorem m64Intrinsic_exists_local_arc_retained_domain_with_sine_focusing
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (height : ℝ → ℝ) {l u : ℝ} (hlu : l < u)
    {X : Set ℝ} (hX : X ⊆ Ioo l u)
    {rho kappa : ℝ} (hrho : 0 < rho) (hkappa : 0 < kappa)
    (hangle : kappa * rho ≤ Real.pi / 4)
    (hray : ∀ a ∈ X, InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)))
    (hfocus : ∀ a ∈ X, ∀ b ∈ X, a < b →
      (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b), e !₂[a, t] = e !₂[b, s]) →
      Real.cos (kappa * rho) * intrinsicBoundaryLength N.metric 1 a b ≤
        (Real.sin (kappa * rho) / kappa) *
          intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc l u ∧
      (∫ x in E, intrinsicBoundarySpeed N.metric 1 x) ≤
        8 * rho * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 l u ∧
      InjOn e {z : AnnulusCoordinates | z 0 ∈ X \ E ∧ z 1 ∈ Icc 0 (height (z 0))} := by
  obtain ⟨E, hE, hEsub, hbound, hinj⟩ :=
    m64Intrinsic_exists_local_arc_retained_normal_domain N e height hlu hX
      (A := 2 * rho) (τ := 4) (by positivity) (by norm_num) hray
      (fun a ha b hb hab hmeet =>
        m64Intrinsic_sine_focusing_length_le_twice_radius_turning hrho hkappa hangle
          (m64Intrinsic_boundaryLength_nonneg N 1 a b hab.le)
          (m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 a b hab.le)
          (hfocus a ha b hb hab hmeet))
  refine ⟨E, hE, hEsub, ?_, hinj⟩
  simpa only [show (4 : ℝ) * (2 * rho) = 8 * rho by ring] using hbound

end PoincareConjecture

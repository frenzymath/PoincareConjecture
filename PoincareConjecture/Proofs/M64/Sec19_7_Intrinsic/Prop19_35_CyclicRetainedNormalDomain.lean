import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CyclicFocusingCover
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BoundaryPeriodicity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingLoss

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Matrix

namespace PoincareConjecture

theorem m64Intrinsic_exists_cyclic_boundary_focusing_cover
    (N : IntrinsicAnnulus) {A τ : ℝ} (hA : 0 ≤ A) (hτ : 3 < τ)
    (T : Set (ℝ × ℝ))
    (hT : ∀ p ∈ T, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < rampPeriod)
    (hfocus : ∀ p ∈ T,
      intrinsicBoundaryLength N.metric 1 p.1 p.2 ≤
          A * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 p.1 p.2 ∨
      intrinsicBoundaryLength N.metric 1 p.2 (p.1 + rampPeriod) ≤
          A * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1
            p.2 (p.1 + rampPeriod)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) rampPeriod ∧
      (∀ p ∈ T, Icc p.1 p.2 ⊆ E ∨
        Icc p.2 rampPeriod ∪ Icc 0 p.1 ⊆ E) ∧
      (∫ x in E, intrinsicBoundarySpeed N.metric 1 x) ≤
        (2 * τ * A) *
          intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod := by
  exact m64Intrinsic_exists_cyclic_weighted_focusing_cover
    (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
    (m64Intrinsic_boundarySpeed_pos N (by norm_num : (1 : ℝ) ≠ 0))
    (m64Intrinsic_continuous_turning_density N (by norm_num : (1 : ℝ) ≠ 0))
    (fun _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (m64Intrinsic_boundarySpeed_periodic N 1)
    (m64Intrinsic_turning_density_periodic N (by norm_num : (1 : ℝ) ≠ 0))
    Real.two_pi_pos hA hτ T hT hfocus

theorem m64Intrinsic_exists_cyclic_injective_retained_normal_domain
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (height : ℝ → ℝ) {X : Set ℝ} (hX : X ⊆ Ico (0 : ℝ) rampPeriod)
    {A τ : ℝ} (hA : 0 ≤ A) (hτ : 3 < τ)
    (hray : ∀ a ∈ X, InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)))
    (hfocus : ∀ a ∈ X, ∀ b ∈ X, a < b →
      (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b), e !₂[a, t] = e !₂[b, s]) →
      intrinsicBoundaryLength N.metric 1 a b ≤
          A * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b ∨
      intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) ≤
          A * intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 b (a + rampPeriod)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) rampPeriod ∧
      (∫ x in E, intrinsicBoundarySpeed N.metric 1 x) ≤
        (2 * τ * A) *
          intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod ∧
      InjOn e {z : AnnulusCoordinates | z 0 ∈ X \ E ∧ z 1 ∈ Icc 0 (height (z 0))} := by
  let T : Set (ℝ × ℝ) := {p | p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 < p.2 ∧
    ∃ t ∈ Icc 0 (height p.1), ∃ s ∈ Icc 0 (height p.2), e !₂[p.1, t] = e !₂[p.2, s]}
  have hT (p : ℝ × ℝ) (hp : p ∈ T) :
      0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < rampPeriod :=
    ⟨(hX hp.1).1, hp.2.2.1, (hX hp.2.1).2⟩
  obtain ⟨E, hE, hEsub, hcover, hbound⟩ :=
    m64Intrinsic_exists_cyclic_boundary_focusing_cover N hA hτ T hT
      (fun p hp => hfocus p.1 hp.1 p.2 hp.2.1 hp.2.2.1 hp.2.2.2)
  have hleft (p : ℝ × ℝ) (hp : p ∈ T) : p.1 ∈ E := by
    rcases hcover p hp with hf | hw
    · exact hf ⟨le_rfl, hp.2.2.1.le⟩
    · exact hw (Or.inr ⟨(hX hp.1).1, le_rfl⟩)
  refine ⟨E, hE, hEsub, hbound, ?_⟩
  have hrepr (z : AnnulusCoordinates) : !₂[z 0, z 1] = z := by
    ext i
    fin_cases i <;> rfl
  intro x hx y hy hxy
  have heq : x 0 = y 0 := by
    rcases lt_trichotomy (x 0) (y 0) with hlt | heq | hlt
    · have hpair : (x 0, y 0) ∈ T :=
        ⟨hx.1.1, hy.1.1, hlt, x 1, hx.2, y 1, hy.2, by simpa only [hrepr] using hxy⟩
      exact False.elim (hx.1.2 (hleft _ hpair))
    · exact heq
    · have hpair : (y 0, x 0) ∈ T :=
        ⟨hy.1.1, hx.1.1, hlt, y 1, hy.2, x 1, hx.2, by simpa only [hrepr] using hxy.symm⟩
      exact False.elim (hy.1.2 (hleft _ hpair))
  have hyrepr : !₂[x 0, y 1] = y := by rw [heq, hrepr]
  have ht : x 1 = y 1 := hray (x 0) hx.1.1 hx.2
    (by simpa only [heq] using hy.2) (by simpa only [hrepr, hyrepr] using hxy)
  ext i
  fin_cases i
  · exact heq
  · exact ht

theorem m64Intrinsic_exists_cyclic_retained_domain_with_focusing_loss
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (height : ℝ → ℝ) {X : Set ℝ} (hX : X ⊆ Ico (0 : ℝ) rampPeriod)
    {delta r R kappa : ℝ} (hdelta : 0 < delta) (hr : 0 < r)
    (hfirst : r < intrinsicBoundaryLength N.metric 1 0 rampPeriod)
    (hturn : N.SmallBoundaryTurning delta r)
    (hR : 0 < R) (hkappa : 0 < kappa) (hangle : kappa * R ≤ Real.pi / 4)
    (hsmall : R ≤ 3 * r / (1600 * delta))
    (hray : ∀ a ∈ X, InjOn (fun t => e !₂[a, t]) (Icc 0 (height a)))
    (hfocus : ∀ a ∈ X, ∀ b ∈ X, a < b →
      (∃ t ∈ Icc 0 (height a), ∃ s ∈ Icc 0 (height b), e !₂[a, t] = e !₂[b, s]) →
      Real.cos (kappa * R) * intrinsicBoundaryLength N.metric 1 a b ≤
          (Real.sin (kappa * R) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 a b ∨
      Real.cos (kappa * R) * intrinsicBoundaryLength N.metric 1 b (a + rampPeriod) ≤
          (Real.sin (kappa * R) / kappa) *
            intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 b (a + rampPeriod)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc (0 : ℝ) rampPeriod ∧
      (∫ x in E, intrinsicBoundarySpeed N.metric 1 x) <
        3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 ∧
      InjOn e {z : AnnulusCoordinates | z 0 ∈ X \ E ∧ z 1 ∈ Icc 0 (height (z 0))} := by
  obtain ⟨E, hE, hEsub, hbound, hinj⟩ :=
    m64Intrinsic_exists_cyclic_injective_retained_normal_domain N e height hX
      (A := 2 * R) (τ := 4) (by positivity) (by norm_num) hray (by
        intro a ha b hb hab hmeet
        rcases hfocus a ha b hb hab hmeet with hf | hw
        · exact Or.inl (m64Intrinsic_sine_focusing_length_le_twice_radius_turning
            hR hkappa hangle (m64Intrinsic_boundaryLength_nonneg N 1 a b hab.le)
            (m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 a b hab.le) hf)
        · have hwrap : b ≤ a + rampPeriod := by
            have ha0 := (hX ha).1
            have hbP := (hX hb).2
            linarith
          exact Or.inr (m64Intrinsic_sine_focusing_length_le_twice_radius_turning
            hR hkappa hangle
            (m64Intrinsic_boundaryLength_nonneg N 1 b (a + rampPeriod) hwrap)
            (m64Intrinsic_geodesicCurvatureIntegral_nonneg N 1 b (a + rampPeriod) hwrap) hw))
  refine ⟨E, hE, hEsub, ?_, hinj⟩
  have hturning := m64Intrinsic_total_turning_lt N hdelta hr hfirst hturn
  have hcoefficient : (2 * 4 * (2 * R)) * (2 * delta / r) ≤ (3 / 50 : ℝ) := by
    have hscaled := (le_div_iff₀ (by positivity : 0 < 1600 * delta)).mp hsmall
    calc
      _ = (32 * R * delta) / r := by ring
      _ ≤ 3 / 50 := (div_le_iff₀ hr).mpr (by nlinarith only [hscaled])
  calc
    _ ≤ (2 * 4 * (2 * R)) *
        intrinsicGeodesicCurvatureIntegral N.metric N.connection 1 0 rampPeriod := hbound
    _ < (2 * 4 * (2 * R)) * ((2 * delta / r) *
        intrinsicBoundaryLength N.metric 1 0 rampPeriod) :=
      mul_lt_mul_of_pos_left hturning (by positivity)
    _ ≤ 3 * intrinsicBoundaryLength N.metric 1 0 rampPeriod / 50 := by
      have h := mul_le_mul_of_nonneg_right hcoefficient (hr.trans hfirst).le
      nlinarith only [h]

end PoincareConjecture

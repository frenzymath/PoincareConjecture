import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.WeakReplacement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology Bundle

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem laplacian_eq_zero_of_smooth_distributional
    (hΩ : IsOpen Ω) {U : M → ℝ}
    (hUs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω)
    (hweak : ∀ f : EnergyTest D Ω,
      (∫ x, U x * D.laplacian f x ∂g.volumeMeasure) = 0) :
    ∀ x ∈ Ω, D.laplacian U x = 0 := by
  intro x hx
  obtain ⟨V, hVs, hVc, -, hVU⟩ := exists_compact_smooth_germ hΩ hUs hx
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (inter_mem (hΩ.mem_nhds hx) hVU)
  let R : M → ℝ := D.laplacian V
  have hRs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R := D.contMDiff_laplacian hVs
  let f : EnergyTest D Ω := ⟨fun y => b y * R y,
    b.contMDiff.mul hRs, b.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans (fun y hy => (hb hy).1)⟩
  have htest : (∫ y, V y * D.laplacian f y ∂g.volumeMeasure) = 0 := by
    rw [← hweak f]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ tsupport (D.laplacian f)
    · rw [(hb (tsupport_mul_subset_left (D.tsupport_laplacian_subset f hy))).2]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hgreen := integral_mul_laplacian_comm_of_compact_tests (D := D)
    f.smooth hVs f.hasCompactSupport hVc
  have hzero : (∫ y, b y * (R y * R y) ∂g.volumeMeasure) = 0 := by
    calc
      _ = ∫ y, f y * D.laplacian V y ∂g.volumeMeasure := by
        congr 1
        funext y
        change b y * (R y * R y) = (b y * R y) * R y
        ring
      _ = 0 := hgreen.trans htest
  have hRx : R x = 0 := by
    by_contra hRx
    let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
    have hpos := integral_pos_of_integrable_nonneg_nonzero (μ := g.volumeMeasure)
      (b.continuous.mul (hRs.continuous.mul hRs.continuous))
      ((b.continuous.mul (hRs.continuous.mul hRs.continuous)).integrable_of_hasCompactSupport
        b.hasCompactSupport.mul_right)
      (fun y => mul_nonneg b.nonneg (mul_self_nonneg (R y)))
      (x := x) (by simpa only [Pi.mul_apply, b.eq_one, one_mul] using mul_ne_zero hRx hRx)
    exact hpos.ne' hzero
  exact (D.laplacian_eq_of_eventuallyEq hVU).symm.trans hRx

theorem laplacian_eq_zero_of_smooth_weakHarmonicReplacement
    (hΩ : IsOpen Ω) (q : Lp ℝ 2 g.volumeMeasure) (w : H1Zero D Ω)
    (hweak : IsWeakHarmonicReplacement q w) {U : M → ℝ}
    (hUs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω)
    (hU : U =ᵐ[g.volumeMeasure.restrict Ω] (q + toL2 D Ω w : Lp ℝ 2 g.volumeMeasure)) :
    ∀ x ∈ Ω, D.laplacian U x = 0 := by
  apply laplacian_eq_zero_of_smooth_distributional hΩ hUs
  intro f
  have heq := integral_mul_eq_of_ae_eq_on hΩ hU
    ((D.tsupport_laplacian_subset f).trans f.support_subset)
  have h := hweak f
  rw [inner_laplacianLp_eq_integral] at h
  simpa only [mul_comm] using heq.trans (by simpa only [mul_comm] using h)

end PoincareConjecture.LeviCivitaData.Dirichlet

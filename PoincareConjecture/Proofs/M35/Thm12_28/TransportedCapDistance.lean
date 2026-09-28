import PoincareConjecture.Proofs.M35.Thm12_28.CompactMetricComparison
import PoincareConjecture.Proofs.M13.Length

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N]

theorem tangentNorm_pullback_le_of_quadratic_le
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N)
    (x : M) (v : TangentSpace (𝓡 3) x) {Q A : ℝ} (hQ : 0 < Q) (hA : 0 ≤ A)
    (hbound : Q * h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
      (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ A * g.inner x v v) :
    h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
      Real.sqrt (A / Q) * g.tangentNorm x v := by
  have hdiv : h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
      (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ A / Q * g.inner x v v := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hQ).mpr
    simpa only [mul_comm Q] using hbound
  exact (Real.sqrt_le_sqrt hdiv).trans_eq (Real.sqrt_mul (div_nonneg hA hQ.le) _)

theorem pathELength_comp_le_of_tangentNorm_le
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N)
    {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C * g.tangentNorm x v)
    (gamma : ℝ → M) (a b : ℝ)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc a b))
    (himage : MapsTo gamma (Icc a b) U) :
    h.pathELength (f ∘ gamma) a b ≤ ENNReal.ofReal C * g.pathELength gamma a b := by
  rw [M13.pathELength_eq_lintegral_tangentNorm, M13.pathELength_eq_lintegral_tangentNorm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro s hs
  have hsI : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
  have hgammaAt := ((hgamma.mdifferentiableOn one_ne_zero) s hsI).mdifferentiableAt
    (Icc_mem_nhds hs.1 hs.2)
  have hfAt := (hf.contMDiffAt (hU.mem_nhds (himage hsI))).mdifferentiableAt (by simp)
  have hd := congrArg (fun A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 3) => A 1)
    (mfderiv_comp s hfAt hgammaAt)
  have hnorm := congrArg (fun v : EuclideanSpace ℝ (Fin 3) =>
    h.tangentNorm (f (gamma s)) v) hd
  exact (ENNReal.ofReal_le_ofReal
    (hnorm.trans_le (hbound (gamma s) (himage hsI) _))).trans_eq (ENNReal.ofReal_mul hC)

theorem intrinsicEDist_image_le
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N)
    {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C * g.tangentNorm x v)
    (x y : M) :
    intrinsicEDist h (f '' U) (f x) (f y) ≤ ENNReal.ofReal C * intrinsicEDist g U x y := by
  have hc0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  apply (ENNReal.inv_mul_le_iff hc0 ENNReal.ofReal_ne_top).mp
  apply le_sInf
  rintro L ⟨gamma, hgamma, hstart, hend, himage, rfl⟩
  have hmaps : MapsTo gamma (Icc (0 : ℝ) 1) U := fun s hs => himage ⟨s, hs, rfl⟩
  have hlength := pathELength_comp_le_of_tangentNorm_le g h f hU hf hC.le
    hbound gamma 0 1 hgamma hmaps
  have hd : intrinsicEDist h (f '' U) (f x) (f y) ≤ h.pathELength (f ∘ gamma) 0 1 := by
    apply sInf_le
    refine ⟨f ∘ gamma, (hf.of_le (by simp)).comp hgamma hmaps,
      congrArg f hstart, congrArg f hend, ?_, rfl⟩
    rintro z ⟨s, hs, rfl⟩
    exact ⟨gamma s, hmaps hs, rfl⟩
  exact (mul_le_mul' le_rfl (hd.trans hlength)).trans_eq
    (ENNReal.inv_mul_cancel_left hc0 ENNReal.ofReal_ne_top)

theorem intrinsicDiameter_image_le
    (g : RiemannianMetric 3 M) (h : RiemannianMetric 3 N) (f : M → N)
    {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C * g.tangentNorm x v) :
    intrinsicDiameter h (f '' U) ≤ ENNReal.ofReal C * intrinsicDiameter g U := by
  apply sSup_le
  rintro d ⟨⟨⟨_, hx⟩, ⟨_, hy⟩⟩, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact (intrinsicEDist_image_le g h f hU hf hC hbound x y).trans
    (mul_le_mul' le_rfl (le_sSup ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩))

end PoincareConjecture.M35

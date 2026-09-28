import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.ContinuousOperator
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.ClassicalEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

private theorem weak_forcing_integral_laplacian_test
    (u v : H1Zero D Ω)
    (heq : ∀ w : H1Zero D Ω, ⟪u, w⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω w⟫_ℝ =
      ⟪toL2 D Ω v, toL2 D Ω w⟫_ℝ)
    (φ : EnergyTest D Ω) :
    (∫ x, D.laplacian φ x * toL2 D Ω u x ∂g.volumeMeasure) =
      -(∫ x, φ x * toL2 D Ω v x ∂g.volumeMeasure) := by
  have h := heq (φ : H1Zero D Ω)
  rw [real_inner_comm (φ : H1Zero D Ω) u, inner_test_eq_oneSubLaplacian, toL2_coe] at h
  have hleft : ⟪φ.oneSubLaplacian, toL2 D Ω u⟫_ℝ =
      (∫ x, φ x * toL2 D Ω u x ∂g.volumeMeasure) -
        ∫ x, D.laplacian φ x * toL2 D Ω u x ∂g.volumeMeasure := by
    rw [L2.inner_def]
    calc
      (∫ x, inner ℝ (φ.oneSubLaplacian x) (toL2 D Ω u x) ∂g.volumeMeasure) =
          ∫ x, (φ x - D.laplacian φ x) * toL2 D Ω u x ∂g.volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [φ.oneSubLaplacian_memLp.coeFn_toLp] with x hx
        rw [show φ.oneSubLaplacian x = φ x - D.laplacian φ x from hx]
        simp [mul_comm]
      _ = _ := by
        have h₁ := φ.memLp.integrable_mul (Lp.memLp (toL2 D Ω u))
        have h₂ := φ.laplacian_memLp.integrable_mul (Lp.memLp (toL2 D Ω u))
        simpa only [Pi.mul_apply, sub_mul] using integral_sub h₁ h₂
  rw [hleft, ← integral_test_mul, ← integral_test_mul] at h
  linarith

private theorem laplacian_eq_neg_of_smooth_forcing
    (hΩ : IsOpen Ω) {U W : M → ℝ}
    (hUs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω)
    (hWs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ W Ω)
    (hweak : ∀ φ : EnergyTest D Ω,
      (∫ x, D.laplacian φ x * U x ∂g.volumeMeasure) =
        -(∫ x, φ x * W x ∂g.volumeMeasure))
    {x : M} (hx : x ∈ Ω) : D.laplacian U x = -W x := by
  obtain ⟨V, hVs, hVc, -, hVU⟩ := exists_compact_smooth_germ hΩ hUs hx
  obtain ⟨Z, hZs, -, -, hZW⟩ := exists_compact_smooth_germ hΩ hWs hx
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (inter_mem (hΩ.mem_nhds hx) (inter_mem hVU hZW))
  let R : M → ℝ := fun y => D.laplacian V y + Z y
  have hRs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R :=
    (D.contMDiff_laplacian hVs).add hZs
  let φ : EnergyTest D Ω := ⟨fun y => b y * R y,
    b.contMDiff.mul hRs, b.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans (fun y hy => (hb hy).1)⟩
  have htestU (ψ : M → ℝ) (hψ : tsupport ψ ⊆ tsupport (φ : M → ℝ)) :
      (∫ y, ψ y * U y ∂g.volumeMeasure) = ∫ y, ψ y * V y ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ tsupport ψ
    · rw [(hb (tsupport_mul_subset_left (hψ hy))).2.1]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have htestW : (∫ y, φ y * W y ∂g.volumeMeasure) =
      ∫ y, φ y * Z y ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ tsupport (φ : M → ℝ)
    · rw [(hb (tsupport_mul_subset_left hy)).2.2]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have heq := hweak φ
  rw [htestU (D.laplacian φ) (D.tsupport_laplacian_subset φ), htestW] at heq
  have hgreen := integral_mul_laplacian_comm_of_compact_tests (D := D)
    φ.smooth hVs φ.hasCompactSupport hVc
  have hzero : (∫ y, b y * (R y * R y) ∂g.volumeMeasure) = 0 := by
    have hi : Integrable (fun y => φ y * D.laplacian V y) g.volumeMeasure :=
      D.integrable_mul_laplacian φ.smooth hVs φ.hasCompactSupport
    have hj : Integrable (fun y => φ y * Z y) g.volumeMeasure :=
      (φ.smooth.continuous.mul hZs.continuous).integrable_of_hasCompactSupport
        φ.hasCompactSupport.mul_right
    calc
      _ = ∫ y, φ y * D.laplacian V y + φ y * Z y ∂g.volumeMeasure := by
        congr 1
        funext y
        change b y * (R y * R y) = (b y * R y) * D.laplacian V y + (b y * R y) * Z y
        dsimp only [R]
        ring
      _ = (∫ y, φ y * D.laplacian V y ∂g.volumeMeasure) +
          ∫ y, φ y * Z y ∂g.volumeMeasure := integral_add hi hj
      _ = 0 := by
        rw [hgreen]
        have hcomm : (∫ y, V y * D.laplacian φ y ∂g.volumeMeasure) =
            ∫ y, D.laplacian φ y * V y ∂g.volumeMeasure := by
          congr 1
          funext y
          ring
        rw [hcomm, heq]
        ring
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
  have hLap := D.laplacian_eq_of_eventuallyEq hVU
  dsimp only [R] at hRx
  rw [hLap, hZW.eq_of_nhds] at hRx
  linarith

variable [NeZero n] (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)

theorem heatPowerContinuous_laplacian (k : ℕ) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (x : M) (hx : x ∈ Ω) :
    D.laplacian (heatPowerContinuous D S k t ht f : M → ℝ) x =
      -heatPowerContinuous D S (k + 1) t ht f x := by
  let hn := Nat.pos_of_ne_zero (NeZero.ne n)
  let u := energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure k t f
  let v := energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure (k + 1) t f
  have hpair (w : H1Zero D Ω) :
      ⟪u, w⟫_ℝ - ⟪toL2 D Ω u, toL2 D Ω w⟫_ℝ =
        ⟪toL2 D Ω v, toL2 D Ω w⟫_ℝ := by
    have h := energyHeatSpectralPower_pairing D Ω hn S.isOpen S.isCompact_closure k ht f w
    rw [← toDomainL2_energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure k ht f,
      ← toDomainL2_energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure (k + 1) ht f,
      inner_toDomainL2 S.isOpen.measurableSet, inner_toDomainL2 S.isOpen.measurableSet] at h
    exact h
  have hae (j : ℕ) : (heatPowerContinuous D S j t ht f : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω]
      toL2 D Ω (energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure j t f) := by
    have h := toDomainL2_ae (energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure j t f)
    rw [toDomainL2_energyHeatSpectralPower D Ω hn S.isOpen S.isCompact_closure j ht f] at h
    exact (heatPowerContinuous_ae D S j t ht f).trans h
  apply laplacian_eq_neg_of_smooth_forcing S.isOpen
    (contMDiffOn_heatPowerContinuous D S k t ht f)
    (contMDiffOn_heatPowerContinuous D S (k + 1) t ht f) _ hx
  intro φ
  rw [integral_mul_eq_of_ae_eq_on S.isOpen (hae k)
    ((D.tsupport_laplacian_subset φ).trans φ.support_subset),
    integral_mul_eq_of_ae_eq_on S.isOpen (hae (k + 1)) φ.support_subset]
  exact weak_forcing_integral_laplacian_test u v hpair φ

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

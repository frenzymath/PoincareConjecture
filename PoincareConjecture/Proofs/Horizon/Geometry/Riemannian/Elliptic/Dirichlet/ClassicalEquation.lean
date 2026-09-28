import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.WeakEquation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff InnerProductSpace Topology Bundle

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

theorem integral_mul_eq_of_ae_eq_on {U V ψ : M → ℝ}
    (hΩ : IsOpen Ω) (hUV : U =ᵐ[g.volumeMeasure.restrict Ω] V)
    (hψ : tsupport ψ ⊆ Ω) :
    (∫ x, ψ x * U x ∂g.volumeMeasure) =
      ∫ x, ψ x * V x ∂g.volumeMeasure := by
  apply integral_congr_ae
  have h := (ae_restrict_iff' hΩ.measurableSet).mp hUV
  filter_upwards [h] with x hx
  by_cases hxΩ : x ∈ Ω
  · rw [hx hxΩ]
  · have hxψ : x ∉ tsupport ψ := fun h => hxΩ (hψ h)
    simp [image_eq_zero_of_notMem_tsupport hxψ]

theorem weakEigen_integral_laplacian_representative
    (hΩ : IsOpen Ω) (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    {U : M → ℝ} (hU : U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D Ω u : M → ℝ))
    (f : EnergyTest D Ω) :
    (∫ x, D.laplacian f x * U x ∂g.volumeMeasure) =
      -lambda * ∫ x, f x * U x ∂g.volumeMeasure := by
  rw [integral_mul_eq_of_ae_eq_on hΩ hU
    ((D.tsupport_laplacian_subset f).trans f.support_subset),
    integral_mul_eq_of_ae_eq_on hΩ hU f.support_subset]
  exact weakEigen_integral_laplacian_test u lambda heigen f

theorem integral_mul_laplacian_comm_of_compact_tests {f h : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hh : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h) :
    (∫ x, f x * D.laplacian h x ∂g.volumeMeasure) =
      ∫ x, h x * D.laplacian f x ∂g.volumeMeasure := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [integral_mul_laplacian_of_compact_test hf hh hfc,
    integral_mul_laplacian_of_compact_test hh hf hhc]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  change inner ℝ (D.gradient f x) (D.gradient h x) =
    inner ℝ (D.gradient h x) (D.gradient f x)
  exact real_inner_comm _ _

omit [MeasurableSpace M] [BorelSpace M] in

theorem exists_compact_smooth_germ (hΩ : IsOpen Ω) {U : M → ℝ}
    (hU : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω) {x : M} (hx : x ∈ Ω) :
    ∃ V : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ V ∧
      HasCompactSupport V ∧ tsupport V ⊆ Ω ∧ V =ᶠ[𝓝 x] U := by
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (hΩ.mem_nhds hx)
  refine ⟨fun y => b y * U y, ?_, b.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans hb, ?_⟩
  · apply contMDiff_of_tsupport
    intro y hy
    have hyΩ := hb (tsupport_mul_subset_left hy)
    exact b.contMDiffAt.mul (hU.contMDiffAt (hΩ.mem_nhds hyΩ))
  · filter_upwards [b.eventuallyEq_one] with y hy
    simp [hy]

theorem volumeMeasure_isOpenPosMeasure : g.volumeMeasure.IsOpenPosMeasure := by
  constructor
  intro W hW hWne hzero
  obtain ⟨x, hx⟩ := hWne
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) x).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  let S := e.source ∩ e ⁻¹' W
  have hS : IsOpen S := e.isOpen_inter_preimage hW
  have hSne : S.Nonempty := by
    refine ⟨e.symm x, e.map_target (mem_chart_source _ _), ?_⟩
    simpa only [mem_preimage, e.right_inv (mem_chart_source _ _)] using hx
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hd (y) (hy : y ∈ S) := g.contDiffAt_pullbackVolumeDensity
    (he.contMDiffAt (e.open_source.mem_nhds hy.1)) (hD.mfderiv_injective hy.1)
  have hcont : ContinuousOn (fun y => ENNReal.ofReal (g.pullbackVolumeDensity e y)) S :=
    fun y hy => (ENNReal.continuous_ofReal.continuousAt.comp (hd y hy).1.continuousAt).continuousWithinAt
  have hvol : g.volumeMeasure (e '' S) = 0 :=
    measure_mono_null (by rintro _ ⟨y, hy, rfl⟩; exact hy.2) hzero
  rw [g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity e he hei
    hS.measurableSet inter_subset_left] at hvol
  have hae := (setLIntegral_eq_zero_iff' hS.measurableSet
    (hcont.aemeasurable hS.measurableSet)).mp hvol
  have hnull : volume S = 0 := by
    apply measure_mono_null (t := {y | ¬ (y ∈ S → ENNReal.ofReal
      (g.pullbackVolumeDensity e y) = 0)}) ?_ (ae_iff.mp hae)
    intro y hy hz
    exact (ENNReal.ofReal_pos.mpr (hd y hy).2).ne' (hz hy)
  exact hS.measure_ne_zero volume hSne hnull

theorem laplacian_eq_of_smooth_representative
    (hΩ : IsOpen Ω) (u : H1Zero D Ω) (lambda : ℝ)
    (heigen : ∀ v : H1Zero D Ω,
      ⟪u, v⟫_ℝ = (1 + lambda) * ⟪toL2 D Ω u, toL2 D Ω v⟫_ℝ)
    {U : M → ℝ} (hUs : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ U Ω)
    (hU : U =ᵐ[g.volumeMeasure.restrict Ω] (toL2 D Ω u : M → ℝ)) :
    ∀ x ∈ Ω, -D.laplacian U x = lambda * U x := by
  intro x hx
  obtain ⟨V, hVs, hVc, -, hVU⟩ := exists_compact_smooth_germ hΩ hUs hx
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp
    (inter_mem (hΩ.mem_nhds hx) hVU)
  let R : M → ℝ := fun y => D.laplacian V y + lambda * V y
  have hRs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ R :=
    (D.contMDiff_laplacian hVs).add (contMDiff_const.mul hVs)
  let f : EnergyTest D Ω := ⟨fun y => b y * R y,
    b.contMDiff.mul hRs, b.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans (fun y hy => (hb hy).1)⟩
  have htest (ψ : M → ℝ) (hψ : tsupport ψ ⊆ tsupport (f : M → ℝ)) :
      (∫ y, ψ y * U y ∂g.volumeMeasure) = ∫ y, ψ y * V y ∂g.volumeMeasure := by
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ tsupport ψ
    · rw [(hb (tsupport_mul_subset_left (hψ hy))).2]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hweak := weakEigen_integral_laplacian_representative hΩ u lambda heigen hU f
  rw [htest (D.laplacian f) (D.tsupport_laplacian_subset f), htest f subset_rfl] at hweak
  have hgreen := integral_mul_laplacian_comm_of_compact_tests (D := D)
    f.smooth hVs f.hasCompactSupport hVc
  have hzero : (∫ y, b y * (R y * R y) ∂g.volumeMeasure) = 0 := by
    have hi : Integrable (fun y => f y * D.laplacian V y) g.volumeMeasure :=
      D.integrable_mul_laplacian f.smooth hVs f.hasCompactSupport
    have hj : Integrable (fun y => f y * V y) g.volumeMeasure :=
      (f.smooth.continuous.mul hVs.continuous).integrable_of_hasCompactSupport
        f.hasCompactSupport.mul_right
    calc
      _ = ∫ y, f y * D.laplacian V y + lambda * (f y * V y) ∂g.volumeMeasure := by
        congr 1
        funext y
        change b y * (R y * R y) = (b y * R y) * D.laplacian V y +
          lambda * ((b y * R y) * V y)
        dsimp only [R]
        ring
      _ = (∫ y, f y * D.laplacian V y ∂g.volumeMeasure) +
          lambda * ∫ y, f y * V y ∂g.volumeMeasure := by
        rw [integral_add hi (hj.const_mul lambda), integral_const_mul]
      _ = 0 := by
        rw [hgreen]
        have hcomm : (∫ y, V y * D.laplacian f y ∂g.volumeMeasure) =
            ∫ y, D.laplacian f y * V y ∂g.volumeMeasure := by
          congr 1
          funext y
          ring
        rw [hcomm, hweak]
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
  have hVal := hVU.eq_of_nhds
  dsimp only [R] at hRx
  rw [hLap, hVal] at hRx
  linarith

end PoincareConjecture.LeviCivitaData.Dirichlet

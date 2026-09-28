import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarPotential
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationPoissonSmooth

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarAnnulus_isOpen : IsOpen scalarAnnulus :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

theorem laplacian_zero_of_smooth_distribution {Ω : Set Plane} (hΩ : IsOpen Ω)
    {U : Plane → ℝ} (hU : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ U Ω)
    (hweak : ∀ f : EnergyTest D Ω,
      (∫ x, D.laplacian f x * U x ∂g.volumeMeasure) = 0) :
    ∀ x ∈ Ω, D.laplacian U x = 0 := by
  intro x hx
  obtain ⟨V, hVs, hVc, -, hVU⟩ := exists_compact_smooth_germ hΩ hU hx
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 2) x).mem_iff.mp
    (inter_mem (hΩ.mem_nhds hx) hVU)
  let R : Plane → ℝ := D.laplacian V
  have hRs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ R := D.contMDiff_laplacian hVs
  let f : EnergyTest D Ω := ⟨fun y => b y * R y,
    b.contMDiff.mul hRs, b.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans (fun y hy => (hb hy).1)⟩
  have htest : (∫ y, D.laplacian f y * U y ∂g.volumeMeasure) =
      ∫ y, D.laplacian f y * V y ∂g.volumeMeasure := by
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
      _ = ∫ y, V y * D.laplacian f y ∂g.volumeMeasure := hgreen
      _ = ∫ y, D.laplacian f y * V y ∂g.volumeMeasure := by
        congr 1
        funext y
        ring
      _ = 0 := htest.symm.trans (hweak f)
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

theorem exists_annular_smooth_harmonic_potential :
    ∃ (H : Plane → ℝ) (w : H1Zero D scalarAnnulus),
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ) ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      ∀ v : H1Zero D scalarAnnulus,
        affineDirichletEnergy D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w ≤
        affineDirichletEnergy D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact v := by
  obtain ⟨w, hw, hmin⟩ := exists_annular_harmonic_potential D
  let q := annularBoundaryExtension
  let hq := annularBoundaryExtension_smooth
  let hqc := annularBoundaryExtension_compact
  let F := boundaryLaplacianL2 D q hq hqc
  let ell := boundaryForcing D scalarAnnulus q hq hqc
  have hforce (v : H1Zero D scalarAnnulus) : gradientEnergy D scalarAnnulus w v = ell v := by
    induction v using Completion.induction_on with
    | hp => exact isClosed_eq ((gradientEnergy D scalarAnnulus) w).continuous ell.continuous
    | ih f =>
      change gradientEnergy D scalarAnnulus w f = boundaryForcing D scalarAnnulus q hq hqc f
      rw [boundaryForcing_eq_neg_gradient]
      exact eq_neg_of_add_eq_zero_left (hw f)
  have hF : (F : Plane → ℝ) =ᵐ[g.volumeMeasure] D.laplacian q :=
    ((D.continuous_laplacian hq).memLp_of_hasCompactSupport
      (D.hasCompactSupport_laplacian hqc)).coeFn_toLp
  obtain ⟨W, hWs, hWae⟩ := M60.exists_smooth_poisson_representative
    (D := D) (by norm_num : 0 < 2) scalarAnnulus_isOpen w F (D.laplacian q)
    (D.contMDiff_laplacian hq) hF hforce
  let H : Plane → ℝ := fun x => q x + W x
  have hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus :=
    hq.contMDiffOn.add hWs
  have hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus q hq hqc w : Plane → ℝ) := by
    filter_upwards [hWae, ae_restrict_of_ae (Lp.coeFn_add
      ((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q)
      (toL2 D scalarAnnulus w)),
      ae_restrict_of_ae ((hq.continuous.memLp_of_hasCompactSupport hqc).coeFn_toLp)]
      with x hxW hxadd hxq
    change q x + W x = _
    change _ = ((((hq.continuous.memLp_of_hasCompactSupport hqc).toLp q) +
      toL2 D scalarAnnulus w : Lp ℝ 2 g.volumeMeasure) : Plane → ℝ) x
    rw [hxadd, Pi.add_apply, hxq, hxW]
  refine ⟨H, w, hHs, hHae, ?_, hmin⟩
  apply laplacian_zero_of_smooth_distribution D scalarAnnulus_isOpen hHs
  intro f
  rw [integral_mul_eq_of_ae_eq_on scalarAnnulus_isOpen hHae
    ((D.tsupport_laplacian_subset f).trans f.support_subset)]
  have hp := scalarPotential_laplacian_pairing D q hq hqc w f
  rw [boundaryForcing_eq_neg_gradient] at hp
  have hz : (∫ x, scalarPotentialL2 D scalarAnnulus q hq hqc w x *
      D.laplacian f x ∂g.volumeMeasure) = 0 := by
    linarith [hw f]
  simpa only [mul_comm] using hz

end PoincareConjecture.M64Uniformization

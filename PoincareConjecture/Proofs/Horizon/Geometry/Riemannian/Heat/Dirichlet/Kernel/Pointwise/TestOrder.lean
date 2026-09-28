import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise







set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}


theorem nonneg_of_integral_mul_test_nonneg
    (hΩ : IsOpen Ω) {F : M → ℝ} (hF : Continuous F)
    (hpos : ∀ φ : EnergyTest D Ω,
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in Ω, F x * φ x ∂g.volumeMeasure) :
    ∀ x ∈ Ω, 0 ≤ F x := by
  intro x hx
  by_contra hneg
  have hFx : F x < 0 := lt_of_not_ge hneg
  have hU : Ω ∩ F ⁻¹' Iio 0 ∈ 𝓝 x :=
    inter_mem (hΩ.mem_nhds hx) (hF.continuousAt.preimage_mem_nhds (Iio_mem_nhds hFx))
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp hU
  let φ : EnergyTest D Ω :=
    ⟨b, b.contMDiff, b.hasCompactSupport, hb.trans inter_subset_left⟩
  let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
  have hnonneg : 0 ≤ fun y => -(F y * b y) := by
    intro y
    by_cases hy : y ∈ tsupport (b : M → ℝ)
    · exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (hb hy).2.le b.nonneg)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  have hp : 0 < (∫ y, -(F y * b y) ∂g.volumeMeasure) :=
    (hF.mul b.contMDiff.continuous).neg.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := x) b.hasCompactSupport.mul_left.neg hnonneg (by
        simpa only [Pi.neg_apply, Pi.mul_apply, b.eq_one, mul_one, neg_ne_zero]
          using ne_of_lt hFx)
  have heq : (∫ y in Ω, F y * φ y ∂g.volumeMeasure) =
      ∫ y, F y * b y ∂g.volumeMeasure := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyb : y ∉ tsupport (b : M → ℝ) := fun hz => hy (hb hz).1
    simp only [φ, image_eq_zero_of_notMem_tsupport hyb, mul_zero]
  rw [integral_neg] at hp
  have hp' := hpos φ (fun _ => b.nonneg)
  rw [heq] at hp'
  linarith


theorem integral_heatKernelContinuous_test [NeZero n] (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (t : ℝ) (ht : 0 < t)
    (x : M) (φ : EnergyTest D Ω) :
    (∫ y in Ω, heatKernelContinuous D S t ht x y * φ y ∂g.volumeMeasure) =
      Boundary.heatPowerContinuous D S 0 t ht
        (toDomainL2 D Ω (φ : H1Zero D Ω)) x := by
  rw [← integral_heatKernelContinuous_mul D S t ht x]
  apply integral_congr_ae
  have hφ : (toDomainL2 D Ω (φ : H1Zero D Ω) : M → ℝ) =ᵐ[
      g.volumeMeasure.restrict Ω] (φ : M → ℝ) :=
    (toDomainL2_ae (φ : H1Zero D Ω)).trans
      (ae_restrict_of_ae (by rw [toL2_coe]; exact φ.memLp.coeFn_toLp))
  filter_upwards [hφ] with y hy
  rw [hy]

end PoincareConjecture.LeviCivitaData.Dirichlet

import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Integral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Time
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.TestOrder
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Initial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Mass








set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

private theorem tendsto_integral_heatKernelContinuousTime_test (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (φ : EnergyTest D Ω) (x : M) :
    Tendsto (fun t : ℝ => ∫ y in Ω, heatKernelContinuousTime D S t x y * φ y ∂g.volumeMeasure)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (φ x)) := by
  have h := (Boundary.tendstoUniformly_heat_test D S φ).tendsto_at x
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [heatKernelContinuousTime_of_pos D S ht,
    Boundary.heatPowerContinuousTime_of_pos D S 0 ht,
    integral_heatKernelContinuous_test D S t ht x φ]

private theorem integral_heatKernelContinuous_affine_test (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (t : ℝ) (ht : 0 < t)
    (x : M) (φ : EnergyTest D Ω) (a c : ℝ) :
    (∫ y in Ω, heatKernelContinuous D S t ht x y * (a * φ y + c) ∂g.volumeMeasure) =
      a * (∫ y in Ω, heatKernelContinuous D S t ht x y * φ y ∂g.volumeMeasure) +
      c * (∫ y in Ω, heatKernelContinuous D S t ht x y ∂g.volumeMeasure) := by
  have h₁ := integrable_heatKernelContinuous_mul_of_continuousOn D S t ht x
    φ.smooth.continuous.continuousOn
  have h₂ := integrable_heatKernelContinuous D S t ht x
  calc
    _ = ∫ y in Ω, a * (heatKernelContinuous D S t ht x y * φ y) +
        c * heatKernelContinuous D S t ht x y ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by ring
    _ = _ := by rw [integral_add (h₁.const_mul a) (h₂.const_mul c),
      integral_const_mul, integral_const_mul]

omit [MeasurableSpace M] [BorelSpace M] in
private theorem exists_affine_test_bounds (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) {φ : M → ℝ}
    (hφ : ContinuousOn φ (closure Ω)) (x : M) (hx : x ∈ Ω)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : EnergyTest D Ω, b x = 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ y ∈ Ω, (φ x - ε + C) * b y - C ≤ φ y ∧
        φ y ≤ (φ x + ε - C) * b y + C := by
  obtain ⟨C₀, hC₀⟩ := S.isCompact_closure.bddAbove_image hφ.norm
  let C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (y : M) (hy : y ∈ Ω) : -C ≤ φ y ∧ φ y ≤ C := by
    have h := (hC₀ (mem_image_of_mem (fun z => ‖φ z‖) (subset_closure hy))).trans
      (le_max_left C₀ 0)
    exact abs_le.mp h
  have hcont : ContinuousAt φ x := hφ.continuousAt
    (mem_of_superset (S.isOpen.mem_nhds hx) subset_closure)
  have hU : Ω ∩ φ ⁻¹' Ioo (φ x - ε) (φ x + ε) ∈ 𝓝 x :=
    inter_mem (S.isOpen.mem_nhds hx) (hcont.preimage_mem_nhds
      (Ioo_mem_nhds (by linarith) (by linarith)))
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) x).mem_iff.mp hU
  refine ⟨⟨b, b.contMDiff, b.hasCompactSupport, hb.trans inter_subset_left⟩,
    b.eq_one, C, hC, ?_⟩
  intro y hy
  obtain ⟨hlo, hhi⟩ := hbound y hy
  by_cases hby : b y = 0
  · simpa only [hby, mul_zero, zero_sub, zero_add] using And.intro hlo hhi
  · have hyb : y ∈ tsupport (b : M → ℝ) := subset_tsupport _ hby
    obtain ⟨hnear₁, hnear₂⟩ := (hb hyb).2
    have hb₀ : 0 ≤ b y := b.nonneg
    have hb₁ : 0 ≤ 1 - b y := sub_nonneg.mpr b.le_one
    constructor
    · nlinarith [mul_nonneg hb₀ (sub_nonneg.mpr hnear₁.le),
        mul_nonneg hb₁ (show 0 ≤ φ y + C by linarith)]
    · nlinarith [mul_nonneg hb₀ (sub_nonneg.mpr hnear₂.le),
        mul_nonneg hb₁ (sub_nonneg.mpr hhi)]

private theorem integral_heatKernelContinuous_between (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) {φ : M → ℝ}
    (hφ : ContinuousOn φ (closure Ω)) (x : M) (b : EnergyTest D Ω)
    (a₁ a₂ C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y ∈ Ω, a₁ * b y - C ≤ φ y ∧ φ y ≤ a₂ * b y + C)
    (t : ℝ) (ht : 0 < t) :
    a₁ * (∫ y in Ω, heatKernelContinuous D S t ht x y * b y ∂g.volumeMeasure) - C ≤
      (∫ y in Ω, heatKernelContinuous D S t ht x y * φ y ∂g.volumeMeasure) ∧
    (∫ y in Ω, heatKernelContinuous D S t ht x y * φ y ∂g.volumeMeasure) ≤
      a₂ * (∫ y in Ω, heatKernelContinuous D S t ht x y * b y ∂g.volumeMeasure) + C := by
  have hlow := integrable_heatKernelContinuous_mul_of_continuousOn D S t ht x
    ((continuous_const.mul b.smooth.continuous).add continuous_const).continuousOn
      (φ := fun y => a₁ * b y + -C)
  have hhigh := integrable_heatKernelContinuous_mul_of_continuousOn D S t ht x
    ((continuous_const.mul b.smooth.continuous).add continuous_const).continuousOn
      (φ := fun y => a₂ * b y + C)
  have hmid := integrable_heatKernelContinuous_mul_of_continuousOn D S t ht x hφ
  have h₁ := integral_mono_ae hlow hmid (by
    filter_upwards [ae_restrict_mem S.isOpen.measurableSet] with y hy
    exact mul_le_mul_of_nonneg_left (by simpa only [← sub_eq_add_neg] using (hbound y hy).1)
      (heatKernelContinuous_nonneg D S t ht x y))
  have h₂ := integral_mono_ae hmid hhigh (by
    filter_upwards [ae_restrict_mem S.isOpen.measurableSet] with y hy
    exact mul_le_mul_of_nonneg_left (hbound y hy).2
      (heatKernelContinuous_nonneg D S t ht x y))
  rw [integral_heatKernelContinuous_affine_test D S t ht x b a₁ (-C)] at h₁
  rw [integral_heatKernelContinuous_affine_test D S t ht x b a₂ C] at h₂
  have hm := mul_le_mul_of_nonneg_left (heatKernelContinuous_mass_le_one D S t ht x) hC
  constructor <;> nlinarith


theorem tendsto_integral_heatKernelContinuousTime (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω)
    {φ : M → ℝ} (hφ : ContinuousOn φ (closure Ω)) (x : M) (hx : x ∈ Ω) :
    Tendsto (fun t : ℝ => ∫ y in Ω, heatKernelContinuousTime D S t x y * φ y ∂g.volumeMeasure)
      (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (φ x)) := by
  have hbnd (ε : ℝ) (hε : 0 < ε) :
      ∃ L U : ℝ → ℝ,
        Tendsto L (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (φ x - ε)) ∧
        Tendsto U (𝓝[Ioi 0] (0 : ℝ)) (𝓝 (φ x + ε)) ∧
        ∀ᶠ t in 𝓝[Ioi 0] (0 : ℝ),
          L t ≤ (∫ y in Ω, heatKernelContinuousTime D S t x y * φ y ∂g.volumeMeasure) ∧
          (∫ y in Ω, heatKernelContinuousTime D S t x y * φ y ∂g.volumeMeasure) ≤ U t := by
    obtain ⟨b, hbx, C, hC, hbounds⟩ := exists_affine_test_bounds D S hφ x hx ε hε
    let I : ℝ → ℝ := fun t => ∫ y in Ω, heatKernelContinuousTime D S t x y * b y ∂g.volumeMeasure
    have hI : Tendsto I (𝓝[Ioi 0] (0 : ℝ)) (𝓝 1) := by
      simpa only [hbx] using tendsto_integral_heatKernelContinuousTime_test D S b x
    refine ⟨fun t => (φ x - ε + C) * I t - C,
      fun t => (φ x + ε - C) * I t + C, ?_, ?_, ?_⟩
    · simpa only [mul_one, add_sub_cancel_right] using
        (hI.const_mul (φ x - ε + C)).sub_const C
    · simpa only [mul_one, sub_add_cancel] using
        (hI.const_mul (φ x + ε - C)).add_const C
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [I, heatKernelContinuousTime_of_pos D S ht]
      exact integral_heatKernelContinuous_between D S hφ x b
        (φ x - ε + C) (φ x + ε - C) C hC hbounds t ht
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨L, U, hL, -, hbounds⟩ := hbnd ((φ x - a) / 2) (by linarith)
    have hla : a < φ x - (φ x - a) / 2 := by linarith
    filter_upwards [hbounds, hL.eventually (Ioi_mem_nhds hla)] with t ht hlt
    exact lt_of_lt_of_le hlt ht.1
  · intro a ha
    obtain ⟨L, U, -, hU, hbounds⟩ := hbnd ((a - φ x) / 2) (by linarith)
    have hla : φ x + (a - φ x) / 2 < a := by linarith
    filter_upwards [hbounds, hU.eventually (Iio_mem_nhds hla)] with t ht hut
    exact lt_of_le_of_lt ht.2 hut

end PoincareConjecture.LeviCivitaData.Dirichlet

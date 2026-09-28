import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.LowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.ProfileSupport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in

theorem axial_mvfderiv_coordinate_tangent {z : RoundCylinderSpace}
    (hz : z ∈ N.cylinderDomain) (v : RoundCylinderTangent z) :
    mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z v) = v.2 := by
  have hm := (N.coordinate_map_smooth.contMDiffAt
    (N.cylinderDomain_open.mem_nhds hz)).mdifferentiableAt (by simp)
  have hx := N.coordinate_map_mem hz
  have hi := (N.coordinate_inverse_smooth.contMDiffAt
    (N.carrier_open.mem_nhds hx)).mdifferentiableAt (by simp)
  have hs := ((contMDiff_snd (n := ∞)).mdifferentiableAt (by simp)).comp
    (N.coordinate_map z) hi
  have heq : (fun w : RoundCylinderSpace =>
      (N.coordinate_inverse (N.coordinate_map w)).2) =ᶠ[𝓝 z] Prod.snd := by
    filter_upwards [N.cylinderDomain_open.mem_nhds hz] with w hw
    rw [N.coordinate_inverse_coordinate_map hw]
  have hcomp := mfderiv_comp z hs hm
  dsimp only [Function.comp_def] at hcomp
  rw [heq.mfderiv_eq (I := (𝓡 2).prod 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, ℝ)), mfderiv_snd] at hcomp
  exact (congrArg (fun L => L v) hcomp).symm

theorem axial_flux_error_of_gradient_distance (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hx : x ∈ N.carrier)
    {a : TangentSpace (𝓡 3) x} {α σ : ℝ}
    (hclose : g.tangentNorm x (σ • D.gradient f x - a) ≤ α) :
    |σ * mvfderiv (𝓡 3) f x
        (D.gradient (fun y => (N.coordinate_inverse y).2) x) -
      mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x a| ≤
        α / (N.scale * Real.sqrt (1 - N.epsilon)) := by
  have hpos : 0 < N.scale * Real.sqrt (1 - N.epsilon) :=
    mul_pos N.scale_pos (Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half]))
  have h := (N.axial_mvfderiv_bound hx (σ • D.gradient f x - a)).trans hclose
  have hswap : mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x
      (D.gradient f x) = mvfderiv (𝓡 3) f x
        (D.gradient (fun y => (N.coordinate_inverse y).2) x) := by
    rw [← D.inner_gradient, g.symm, D.inner_gradient]
  rw [map_sub, map_smul, smul_eq_mul, hswap] at h
  exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using h)

theorem axialCutoff_flux_lower_of_gradient_distance (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hx : x ∈ N.carrier)
    {a : TangentSpace (𝓡 3) x} {α c σ : ℝ}
    (hclose : g.tangentNorm x (σ • D.gradient f x - a) ≤ α)
    (ha : mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x a = c)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφ' : 0 ≤ deriv φ (N.coordinate_inverse x).2) :
    (c - α / (N.scale * Real.sqrt (1 - N.epsilon))) *
        deriv φ (N.coordinate_inverse x).2 ≤
      σ * mvfderiv (𝓡 3) f x (D.gradient (N.axialCutoff φ) x) := by
  have h := (abs_le.mp (N.axial_flux_error_of_gradient_distance D hx hclose)).1
  rw [ha] at h
  rw [N.gradient_axialCutoff D hφ hx, map_smul, smul_eq_mul]
  have hlow : c - α / (N.scale * Real.sqrt (1 - N.epsilon)) ≤
      σ * mvfderiv (𝓡 3) f x
        (D.gradient (fun y => (N.coordinate_inverse y).2) x) := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hlow hφ']

theorem axialCutoff_flux_lower_of_coordinate_gradient_distance
    (D : LeviCivitaData g) {f : M → ℝ} {z : RoundCylinderSpace}
    (hz : z ∈ N.cylinderDomain) {α c σ : ℝ}
    (hclose : g.tangentNorm (N.coordinate_map z)
      (σ • D.gradient f (N.coordinate_map z) -
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z (0, c)) ≤ α)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφ' : 0 ≤ deriv φ z.2) :
    (c - α / (N.scale * Real.sqrt (1 - N.epsilon))) * deriv φ z.2 ≤
      σ * mvfderiv (𝓡 3) f (N.coordinate_map z)
        (D.gradient (N.axialCutoff φ) (N.coordinate_map z)) := by
  have h := N.axialCutoff_flux_lower_of_gradient_distance D
    (N.coordinate_map_mem hz) hclose (N.axial_mvfderiv_coordinate_tangent hz (0, c)) hφ
  simpa only [N.coordinate_inverse_coordinate_map hz] using
    h (by simpa only [N.coordinate_inverse_coordinate_map hz] using hφ')

theorem ae_axialTransitionProfile_flux_lower_of_gradient_distance
    (D : LeviCivitaData g) {f : M → ℝ} {α c σ L : ℝ} (hL : 0 < L)
    (hclose : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      (N.coordinate_inverse x).2 ∈ Ioo (-L) L →
      ∃ a : TangentSpace (𝓡 3) x,
        g.tangentNorm x (σ • D.gradient f x - a) ≤ α ∧
        mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x a = c) :
    ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      (c - α / (N.scale * Real.sqrt (1 - N.epsilon))) *
          deriv (axialTransitionProfile L) (N.coordinate_inverse x).2 ≤
        σ * mvfderiv (𝓡 3) f x
          (D.gradient (N.axialCutoff (axialTransitionProfile L)) x) := by
  filter_upwards [hclose, ae_restrict_mem N.carrier_open.measurableSet] with x hx hxc
  by_cases hs : (N.coordinate_inverse x).2 ∈ Ioo (-L) L
  · obtain ⟨a, ha, hc⟩ := hx hs
    exact N.axialCutoff_flux_lower_of_gradient_distance D hxc ha hc
      (contDiff_axialTransitionProfile L) (deriv_axialTransitionProfile_nonneg hL _)
  · rw [N.gradient_axialCutoff D (contDiff_axialTransitionProfile L) hxc,
      deriv_axialTransitionProfile_eq_zero_of_not_mem hL hs]
    simp

theorem lintegral_axialTransitionProfile_flux_lower_of_gradient_distance
    (D : LeviCivitaData g) {f : M → ℝ} {α c σ L : ℝ}
    (hL : 0 < L) (hLe : L ≤ N.epsilon⁻¹)
    (hκ : 0 ≤ c - α / (N.scale * Real.sqrt (1 - N.epsilon)))
    (hclose : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      (N.coordinate_inverse x).2 ∈ Ioo (-L) L →
      ∃ a : TangentSpace (𝓡 3) x,
        g.tangentNorm x (σ • D.gradient f x - a) ≤ α ∧
        mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x a = c) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea *
          ENNReal.ofReal (c - α / (N.scale * Real.sqrt (1 - N.epsilon)))) ≤
      ∫⁻ x in N.carrier, ENNReal.ofReal
        (σ * mvfderiv (𝓡 3) f x
          (D.gradient (N.axialCutoff (axialTransitionProfile L)) x))
        ∂g.volumeMeasure := by
  have hpoint := N.ae_axialTransitionProfile_flux_lower_of_gradient_distance D hL hclose
  have hφ := contDiff_axialTransitionProfile L
  have h := N.lintegral_flux_lower_of_pointwise
    (hφ.continuous_deriv (by simp)).measurable hpoint
  rw [lintegral_ofReal_mul_deriv_axialTransitionProfile_of_le hL hLe hκ] at h
  exact h

theorem integral_axialTransitionProfile_flux_lower_of_gradient_distance
    (D : LeviCivitaData g) {f : M → ℝ} {α c σ L : ℝ}
    (hL : 0 < L) (hLe : L ≤ N.epsilon⁻¹)
    (hκ : 0 ≤ c - α / (N.scale * Real.sqrt (1 - N.epsilon)))
    (hclose : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      (N.coordinate_inverse x).2 ∈ Ioo (-L) L →
      ∃ a : TangentSpace (𝓡 3) x,
        g.tangentNorm x (σ • D.gradient f x - a) ≤ α ∧
        mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x a = c)
    (hI : IntegrableOn (fun x => σ * mvfderiv (𝓡 3) f x
      (D.gradient (N.axialCutoff (axialTransitionProfile L)) x))
        N.carrier g.volumeMeasure) :
    (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea.toReal *
          (c - α / (N.scale * Real.sqrt (1 - N.epsilon)))) ≤
      ∫ x in N.carrier, σ * mvfderiv (𝓡 3) f x
        (D.gradient (N.axialCutoff (axialTransitionProfile L)) x) ∂g.volumeMeasure := by
  have hpoint := N.ae_axialTransitionProfile_flux_lower_of_gradient_distance D hL hclose
  have hnonneg : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      0 ≤ σ * mvfderiv (𝓡 3) f x
        (D.gradient (N.axialCutoff (axialTransitionProfile L)) x) := by
    filter_upwards [hpoint] with x hx
    exact (mul_nonneg hκ (deriv_axialTransitionProfile_nonneg hL _)).trans hx
  have h := N.lintegral_axialTransitionProfile_flux_lower_of_gradient_distance
    D hL hLe hκ hclose
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnonneg] at h
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)),
    ENNReal.toReal_ofReal hκ,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)] using hreal

end PoincareConjecture.EpsilonNeck

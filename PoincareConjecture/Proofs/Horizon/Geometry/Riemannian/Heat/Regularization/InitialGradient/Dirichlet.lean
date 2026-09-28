import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Regularization.InitialGradient.Spectral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Regularity.SpatialJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Linearity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

theorem iterate_laplacian_heat_test_sub
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (φ : EnergyTest D Ω) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    EqOn ((D.laplacian)^[j] (fun x =>
      heatPowerContinuous D S 0 t ht (toDomainL2 D Ω (φ : H1Zero D Ω)) x - φ x))
      (fun x => (-1 : ℝ) ^ j *
        (heatPowerContinuous D S j t ht (toDomainL2 D Ω (φ : H1Zero D Ω)) x -
          ((EnergyTest.negLaplacianTest)^[j] φ) x)) Ω := by
  induction j with
  | zero => intro x hx; simp
  | succ j ih =>
    intro x hx
    rw [Function.iterate_succ_apply',
      D.laplacian_eq_of_eventuallyEq
        (Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ω, S.isOpen.mem_nhds hx, ih⟩),
      D.laplacian_const_mul,
      laplacian_sub_on D S.isOpen (contMDiffOn_heatPowerContinuous D S j t ht _)
        (((EnergyTest.negLaplacianTest)^[j] φ).smooth.contMDiffOn) hx,
      heatPowerContinuous_laplacian D S j t ht _ x hx]
    change (-1 : ℝ)^j * (-heatPowerContinuous D S (j+1) t ht _ x -
      D.laplacian ((EnergyTest.negLaplacianTest)^[j] φ) x) =
      (-1 : ℝ)^(j+1) * (heatPowerContinuous D S (j+1) t ht _ x -
        ((EnergyTest.negLaplacianTest)^[j+1] φ) x)
    simp only [Function.iterate_succ_apply', EnergyTest.negLaplacianTest_apply, pow_succ]
    ring

theorem eLpNorm_iterate_laplacian_heat_test_sub_le
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    (φ : EnergyTest D Ω) (j : ℕ) {t : ℝ} (ht : 0 < t) :
    MemLp ((D.laplacian)^[j] (fun x =>
      heatPowerContinuous D S 0 t ht (toDomainL2 D Ω (φ : H1Zero D Ω)) x - φ x))
        2 (g.volumeMeasure.restrict Ω) ∧
    (eLpNorm ((D.laplacian)^[j] (fun x =>
      heatPowerContinuous D S 0 t ht (toDomainL2 D Ω (φ : H1Zero D Ω)) x - φ x))
        2 (g.volumeMeasure.restrict Ω)).toReal ≤
      t * (eLpNorm ((D.laplacian)^[j + 1] (φ : M → ℝ)) 2 g.volumeMeasure).toReal := by
  let hn := Nat.pos_of_ne_zero (NeZero.ne n)
  let ψ := (EnergyTest.negLaplacianTest)^[j] φ
  let f := toDomainL2 D Ω (φ : H1Zero D Ω)
  let w := toDomainL2 D Ω (ψ : H1Zero D Ω)
  let v := heatSemigroup D Ω hn S.isOpen S.isCompact_closure t.toNNReal w - w
  have haeφ : (w : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω] ψ := by
    apply (toDomainL2_ae (ψ : H1Zero D Ω)).trans
    rw [toL2_coe]
    exact ae_restrict_of_ae ψ.memLp.coeFn_toLp
  have hae : ((D.laplacian)^[j] (fun x => heatPowerContinuous D S 0 t ht f x - φ x))
      =ᵐ[g.volumeMeasure.restrict Ω] (fun x => (-1 : ℝ)^j * v x) := by
    have hflow := heatPowerContinuous_ae D S j t ht f
    rw [heatSpectralPower_test_eq_heatSemigroup_iterate hn S.isOpen S.isCompact_closure
      φ j ht] at hflow
    filter_upwards [ae_restrict_mem S.isOpen.measurableSet, hflow, haeφ,
      Lp.coeFn_sub (heatSemigroup D Ω hn S.isOpen S.isCompact_closure t.toNNReal w) w]
      with x hx hflowx hφx hvx
    rw [iterate_laplacian_heat_test_sub D S φ j ht hx]
    change (-1 : ℝ)^j * (heatPowerContinuous D S j t ht f x - ψ x) =
      (-1 : ℝ)^j * v x
    change v x = heatSemigroup D Ω hn S.isOpen S.isCompact_closure t.toNNReal w x - w x at hvx
    rw [hflowx, hvx, hφx]
  refine ⟨(memLp_congr_ae hae).mpr ((Lp.memLp v).const_mul _), ?_⟩
  have heq : eLpNorm (fun x => (-1 : ℝ)^j * v x) 2 (g.volumeMeasure.restrict Ω) =
      eLpNorm (v : M → ℝ) 2 (g.volumeMeasure.restrict Ω) := by
    apply eLpNorm_congr_norm_ae
    filter_upwards [] with x
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [eLpNorm_congr_ae hae, heq, ← Lp.norm_def]
  have h := norm_heatSemigroup_test_sub_le hn S.isOpen S.isCompact_closure ψ t.toNNReal
  rw [Real.coe_toNNReal _ ht.le] at h
  apply h.trans_eq
  congr 1
  rw [show ψ.negLaplacianTest = (EnergyTest.negLaplacianTest)^[j + 1] φ from
    (Function.iterate_succ_apply' _ _ _).symm,
    EnergyTest.norm_toDomainL2_iterate_negLaplacianTest S.isOpen]

end PoincareConjecture.LeviCivitaData.Dirichlet

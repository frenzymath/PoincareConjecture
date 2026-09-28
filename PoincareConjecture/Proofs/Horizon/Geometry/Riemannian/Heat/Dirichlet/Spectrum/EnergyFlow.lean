import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Semigroup
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.EnergyEmbedding
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralSmoothing
import Mathlib.Analysis.InnerProductSpace.Calculus











set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable (D : LeviCivitaData g) (Ω : Set M) (hn : 0 < n)
  (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))


def heatSpectralPower (k : ℕ) (t : ℝ) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] Lp ℝ 2 (g.volumeMeasure.restrict Ω) :=
  Poincare.Analysis.Dirichlet.Spectral.heatPower (eigenbasis D Ω hn hΩ hc)
    (eigenvalueNN D Ω hn hΩ hc) k t

theorem heatSpectralPower_repr (k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (i : EigenIndex D Ω) :
    (eigenbasis D Ω hn hΩ hc).repr (heatSpectralPower D Ω hn hΩ hc k t f) i =
      eigenvalue D Ω i ^ k * Real.exp (-eigenvalue D Ω i * t) *
        (eigenbasis D Ω hn hΩ hc).repr f i :=
  Poincare.Analysis.Dirichlet.Spectral.heatPower_repr _ _ _ ht _ _

theorem heatSpectralPower_zero_eq_heatSemigroup {t : ℝ} (ht : 0 < t) :
    heatSpectralPower D Ω hn hΩ hc 0 t = heatSemigroup D Ω hn hΩ hc t.toNNReal :=
  Poincare.Analysis.Dirichlet.Spectral.heatPower_zero_eq_heat _ _ ht


def energyHeatSpectralPower (k : ℕ) (t : ℝ) :
    Lp ℝ 2 (g.volumeMeasure.restrict Ω) →L[ℝ] H1Zero D Ω :=
  (domainResolvent D Ω).comp
    (heatSpectralPower D Ω hn hΩ hc k t + heatSpectralPower D Ω hn hΩ hc (k + 1) t)

theorem toDomainL2_energyHeatSpectralPower (k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    toDomainL2 D Ω (energyHeatSpectralPower D Ω hn hΩ hc k t f) =
      heatSpectralPower D Ω hn hΩ hc k t f := by
  change domainL2Resolvent D Ω
    (heatSpectralPower D Ω hn hΩ hc k t f +
      heatSpectralPower D Ω hn hΩ hc (k + 1) t f) = _
  apply (eigenbasis D Ω hn hΩ hc).repr.injective
  ext i
  rw [domainL2Resolvent_repr, map_add]
  simp only [lp.coeFn_add, Pi.add_apply, heatSpectralPower_repr D Ω hn hΩ hc k ht,
    heatSpectralPower_repr D Ω hn hΩ hc (k + 1) ht, pow_succ]
  calc
    _ = (i.1.1 * (1 + eigenvalue D Ω i)) *
        (eigenvalue D Ω i ^ k * Real.exp (-eigenvalue D Ω i * t) *
          (eigenbasis D Ω hn hΩ hc).repr f i) := by ring
    _ = _ := by rw [resolvent_eigenvalue_mul_one_add, one_mul]

theorem energyHeatSpectralPower_unique (k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (u : H1Zero D Ω)
    (hu : toDomainL2 D Ω u = heatSpectralPower D Ω hn hΩ hc k t f) :
    u = energyHeatSpectralPower D Ω hn hΩ hc k t f := by
  apply toDomainL2_injective_of_local_green hΩ.measurableSet
  rw [hu, toDomainL2_energyHeatSpectralPower D Ω hn hΩ hc k ht]

theorem energyHeatSpectralPower_pairing (k : ℕ) {t : ℝ} (_ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (v : H1Zero D Ω) :
    ⟪energyHeatSpectralPower D Ω hn hΩ hc k t f, v⟫_ℝ -
      ⟪heatSpectralPower D Ω hn hΩ hc k t f, toDomainL2 D Ω v⟫_ℝ =
      ⟪heatSpectralPower D Ω hn hΩ hc (k + 1) t f, toDomainL2 D Ω v⟫_ℝ := by
  change ⟪domainResolvent D Ω (_ + _), v⟫_ℝ - _ = _
  rw [domainResolvent_inner, inner_add_left]
  convert! add_sub_cancel_left
    ⟪heatSpectralPower D Ω hn hΩ hc k t f, toDomainL2 D Ω v⟫_ℝ
    ⟪heatSpectralPower D Ω hn hΩ hc (k + 1) t f, toDomainL2 D Ω v⟫_ℝ using 1

theorem hasDerivAt_heatSpectralPower (k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    HasDerivAt (fun s : ℝ => heatSpectralPower D Ω hn hΩ hc k s f)
      (-heatSpectralPower D Ω hn hΩ hc (k + 1) t f) t :=
  Poincare.Analysis.Dirichlet.Spectral.hasDerivAt_heatPower_apply _ _ _ ht _

theorem hasDerivAt_energyHeatSpectralPower (k : ℕ) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    HasDerivAt (fun s : ℝ => energyHeatSpectralPower D Ω hn hΩ hc k s f)
      (-energyHeatSpectralPower D Ω hn hΩ hc (k + 1) t f) t := by
  have h := (hasDerivAt_heatSpectralPower D Ω hn hΩ hc k ht f).add
    (hasDerivAt_heatSpectralPower D Ω hn hΩ hc (k + 1) ht f)
  have hr := (domainResolvent D Ω).hasFDerivAt.comp_hasDerivAt t h
  simpa only [Function.comp_def, Pi.add_apply, map_add, map_neg, ← neg_add,
    energyHeatSpectralPower, ContinuousLinearMap.comp_apply, add_apply]
    using hr

theorem norm_heatSpectralPower_le (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖heatSpectralPower D Ω hn hΩ hc k t‖ ≤ (k.factorial : ℝ) / t ^ k :=
  Poincare.Analysis.Dirichlet.Spectral.norm_heatPower_le _ _ _ ht

theorem norm_energyHeatSpectralPower_le (k : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖energyHeatSpectralPower D Ω hn hΩ hc k t‖ ≤
      (k.factorial : ℝ) / t ^ k + ((k + 1).factorial : ℝ) / t ^ (k + 1) := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_right norm_domainResolvent_le (norm_nonneg _)).trans
  rw [one_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_heatSpectralPower_le D Ω hn hΩ hc k ht)
    (norm_heatSpectralPower_le D Ω hn hΩ hc (k + 1) ht))

theorem hasDerivAt_heatSemigroup {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    HasDerivAt (fun s : ℝ => heatSemigroup D Ω hn hΩ hc s.toNNReal f)
      (-heatSpectralPower D Ω hn hΩ hc 1 t f) t :=
  Poincare.Analysis.Dirichlet.Spectral.hasDerivAt_heat_apply _ _ ht _

theorem hasDerivAt_heatSemigroup_pairing {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (v : H1Zero D Ω) :
    HasDerivAt (fun s : ℝ =>
      ⟪heatSemigroup D Ω hn hΩ hc s.toNNReal f, toDomainL2 D Ω v⟫_ℝ)
      (⟪heatSemigroup D Ω hn hΩ hc t.toNNReal f, toDomainL2 D Ω v⟫_ℝ -
        ⟪energyHeatSpectralPower D Ω hn hΩ hc 0 t f, v⟫_ℝ) t := by
  have h := (hasDerivAt_heatSemigroup D Ω hn hΩ hc ht f).inner ℝ
    (hasDerivAt_const t (toDomainL2 D Ω v))
  simp only [inner_zero_right, zero_add, inner_neg_left] at h
  convert! h using 1
  have he := energyHeatSpectralPower_pairing D Ω hn hΩ hc 0 ht f v
  rw [heatSpectralPower_zero_eq_heatSemigroup D Ω hn hΩ hc ht] at he
  simp only [Nat.zero_add] at he
  linarith



theorem hasDerivAt_heatSemigroup_integral_test {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) (φ : EnergyTest D Ω) :
    HasDerivAt (fun s : ℝ => ∫ x in Ω,
      φ x * heatSemigroup D Ω hn hΩ hc s.toNNReal f x ∂g.volumeMeasure)
      (∫ x in Ω, D.laplacian φ x *
        heatSemigroup D Ω hn hΩ hc t.toNNReal f x ∂g.volumeMeasure) t := by
  have h := hasDerivAt_heatSemigroup_pairing D Ω hn hΩ hc ht f (φ : H1Zero D Ω)
  simp only [inner_toDomainL2_test] at h
  have he := inner_energy_test_eq_domain_integral hΩ.measurableSet
    (energyHeatSpectralPower D Ω hn hΩ hc 0 t f) φ
  rw [toDomainL2_energyHeatSpectralPower D Ω hn hΩ hc 0 ht,
    heatSpectralPower_zero_eq_heatSemigroup D Ω hn hΩ hc ht] at he
  have hi₁ := (φ.memLp.restrict Ω).integrable_mul
    (Lp.memLp (heatSemigroup D Ω hn hΩ hc t.toNNReal f))
  have hi₂ := (φ.laplacian_memLp.restrict Ω).integrable_mul
    (Lp.memLp (heatSemigroup D Ω hn hΩ hc t.toNNReal f))
  simp only [sub_mul] at he
  have he' : ⟪energyHeatSpectralPower D Ω hn hΩ hc 0 t f, (φ : H1Zero D Ω)⟫_ℝ =
      (∫ x in Ω, φ x * heatSemigroup D Ω hn hΩ hc t.toNNReal f x ∂g.volumeMeasure) -
        ∫ x in Ω, D.laplacian φ x *
          heatSemigroup D Ω hn hΩ hc t.toNNReal f x ∂g.volumeMeasure := by
    refine he.trans ?_
    convert! integral_sub hi₁ hi₂ using 1
  rw [he'] at h
  convert! h using 1
  ring

end PoincareConjecture.LeviCivitaData.Dirichlet

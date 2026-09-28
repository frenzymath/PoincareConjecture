import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.ResolventPowers.Continuous
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Boundary.Regularity.Time
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.ResolventPowers








set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology BoundedContinuousFunction NNReal

namespace PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}


theorem exists_continuous_heat_test (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (φ : EnergyTest D Ω) :
    ∃ F : ℝ → (M →ᵇ ℝ), Continuous F ∧
      (∀ x, F 0 x = φ x) ∧
      ∀ t, 0 < t → F t =
        heatPowerContinuousTime D S 0 t (toDomainL2 D Ω (φ : H1Zero D Ω)) := by
  let hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let J := toDomainL2 D Ω
  let w := J (((EnergyTest.oneSubLaplacianTest)^[n+2]) φ : H1Zero D Ω)
  obtain ⟨T, hT⟩ := exists_resolventPower_continuousLinearMap D S
  let F : ℝ → (M →ᵇ ℝ) := fun t => T (heatSemigroup D Ω hn
    S.isOpen S.isCompact_closure t.toNNReal w)
  have hw : ((domainL2Resolvent D Ω)^(n+2)) w = J (φ : H1Zero D Ω) :=
    domainL2Resolvent_pow_oneSubLaplacianTest S.isOpen (n+2) φ
  have hFzero : F 0 = T w := by simp [F]
  refine ⟨F, T.continuous.comp ((continuous_heatSemigroup D Ω hn
    S.isOpen S.isCompact_closure w).comp continuous_real_toNNReal), ?_, ?_⟩
  · have hae : (T w : M → ℝ) =ᵐ[g.volumeMeasure.restrict Ω] (φ : M → ℝ) := by
      have h := (hT w).1
      rw [hw] at h
      exact h.trans ((toDomainL2_ae (φ : H1Zero D Ω)).trans
        (ae_restrict_of_ae (by rw [toL2_coe]; exact φ.memLp.coeFn_toLp)))
    let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
    have heq := Measure.eqOn_open_of_ae_eq hae S.isOpen
      (T w).continuous.continuousOn φ.smooth.continuous.continuousOn
    intro x
    rw [hFzero]
    by_cases hx : x ∈ Ω
    · exact heq hx
    · rw [(hT w).2 x hx, image_eq_zero_of_notMem_tsupport
        (fun hs => hx (φ.support_subset hs))]
  · intro t ht
    rw [heatPowerContinuousTime_of_pos D S 0 ht]
    apply heatPowerContinuous_unique D S 0 t ht
    · rw [heatSpectralPower_zero_eq_heatSemigroup D Ω hn
        S.isOpen S.isCompact_closure ht, ← hw,
        heatSemigroup_domainL2Resolvent_pow D hn S.isOpen S.isCompact_closure]
      exact (hT _).1
    · exact (hT _).2


theorem tendstoUniformly_heat_test (D : LeviCivitaData g)
    (S : Poincare.Manifold.SmoothDomain n Ω) (φ : EnergyTest D Ω) :
    TendstoUniformly
      (fun t : ℝ => (heatPowerContinuousTime D S 0 t
        (toDomainL2 D Ω (φ : H1Zero D Ω)) : M → ℝ))
      (φ : M → ℝ) (𝓝[Ioi 0] (0 : ℝ)) := by
  obtain ⟨F, hF, hzero, hpos⟩ := exists_continuous_heat_test D S φ
  have h : TendstoUniformly (fun t => (F t : M → ℝ)) (F 0 : M → ℝ)
      (𝓝[Ioi 0] (0 : ℝ)) := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
    ((hF.tendsto 0).mono_left nhdsWithin_le_nhds)
  have heq : (fun t => (F t : M → ℝ)) =ᶠ[𝓝[Ioi 0] (0 : ℝ)]
      (fun t => (heatPowerContinuousTime D S 0 t
        (toDomainL2 D Ω (φ : H1Zero D Ω)) : M → ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact congrArg (fun v : M →ᵇ ℝ => (v : M → ℝ)) (hpos t ht)
  have hzero' : (F 0 : M → ℝ) = φ := funext hzero
  rw [hzero'] at h
  exact (tendstoUniformly_congr heq).mp h

end PoincareConjecture.LeviCivitaData.Dirichlet.Boundary

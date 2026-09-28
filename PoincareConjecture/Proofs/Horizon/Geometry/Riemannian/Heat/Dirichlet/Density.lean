import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Support
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff Bundle InnerProductSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

omit [MeasurableSpace M] [BorelSpace M] in
set_option backward.isDefEq.respectTransparency false in
private theorem domain_isSigmaCompact (g : RiemannianMetric n M)
    (hΩ : IsOpen Ω) (hcompact : IsCompact (closure Ω)) : IsSigmaCompact Ω := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let : SecondCountableTopology Ω :=
    (hcompact.isSeparable.mono subset_closure).secondCountableTopology
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

theorem inner_toDomainL2_test (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω))
    (φ : EnergyTest D Ω) :
    ⟪f, toDomainL2 D Ω (φ : H1Zero D Ω)⟫_ℝ =
      ∫ x in Ω, φ x * f x ∂g.volumeMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hφ : (testToL2 D Ω φ : M → ℝ) =ᵐ[g.volumeMeasure] φ := φ.memLp.coeFn_toLp
  filter_upwards [toDomainL2_ae (φ : H1Zero D Ω), ae_restrict_of_ae hφ]
    with x hx hy
  rw [toL2_coe] at hx
  change inner ℝ (f x) (toDomainL2 D Ω (φ : H1Zero D Ω) x) = φ x * f x
  rw [hx, hy]
  rfl

theorem eq_zero_of_inner_toDomainL2_test_eq_zero
    (hΩ : IsOpen Ω) (hcompact : IsCompact (closure Ω))
    (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω))
    (hf : ∀ φ : EnergyTest D Ω,
      ⟪f, toDomainL2 D Ω (φ : H1Zero D Ω)⟫_ℝ = 0) : f = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  have hloc : LocallyIntegrableOn (f : M → ℝ) Ω (g.volumeMeasure.restrict Ω) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω
  have hzero := hΩ.ae_eq_zero_of_integral_contMDiff_smul_eq_zero' (𝓡 n)
    (domain_isSigmaCompact g hΩ hcompact) hloc
    (fun φ hφ hc hs => by
      let ψ : EnergyTest D Ω := ⟨φ, hφ, hc, hs⟩
      have ht := (inner_toDomainL2_test f ψ).symm.trans (hf ψ)
      simpa only [smul_eq_mul] using ht)
  filter_upwards [hzero, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  exact hx hxΩ

theorem denseRange_toDomainL2 (hΩ : IsOpen Ω) (hcompact : IsCompact (closure Ω)) :
    DenseRange (toDomainL2 D Ω) := by
  have horth : (toDomainL2 D Ω).rangeᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    apply eq_zero_of_inner_toDomainL2_test_eq_zero (D := D) hΩ hcompact
    intro φ
    exact ((toDomainL2 D Ω).range.mem_orthogonal' f).mp hf _
      ⟨(φ : H1Zero D Ω), rfl⟩
  change Dense (↑(toDomainL2 D Ω).range : Set (Lp ℝ 2 (g.volumeMeasure.restrict Ω)))
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]

end PoincareConjecture.LeviCivitaData.Dirichlet

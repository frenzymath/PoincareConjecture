import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Semigroup
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.WeakEquation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace NNReal

namespace PoincareConjecture.LeviCivitaData.Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω : Set M}

def EnergyTest.oneSubLaplacianTest (φ : EnergyTest D Ω) : EnergyTest D Ω :=
  ⟨fun x => φ x - D.laplacian φ x,
    φ.smooth.sub (D.contMDiff_laplacian φ.smooth),
    φ.hasCompactSupport.sub (D.hasCompactSupport_laplacian φ.hasCompactSupport),
    (tsupport_sub _ _).trans (union_subset φ.support_subset
      ((D.tsupport_laplacian_subset φ).trans φ.support_subset))⟩

theorem EnergyTest.toL2_oneSubLaplacianTest (φ : EnergyTest D Ω) :
    toL2 D Ω (φ.oneSubLaplacianTest : H1Zero D Ω) = φ.oneSubLaplacian := by
  rw [toL2_coe]
  apply Lp.ext
  exact φ.oneSubLaplacianTest.memLp.coeFn_toLp.trans
    φ.oneSubLaplacian_memLp.coeFn_toLp.symm

theorem domainResolvent_oneSubLaplacianTest (hΩ : IsOpen Ω) (φ : EnergyTest D Ω) :
    domainResolvent D Ω
      (toDomainL2 D Ω (φ.oneSubLaplacianTest : H1Zero D Ω)) = (φ : H1Zero D Ω) := by
  apply ext_inner_right ℝ
  intro u
  rw [domainResolvent_inner, inner_toDomainL2 hΩ.measurableSet,
    φ.toL2_oneSubLaplacianTest, inner_test_eq_oneSubLaplacian]

theorem domainL2Resolvent_oneSubLaplacianTest (hΩ : IsOpen Ω) (φ : EnergyTest D Ω) :
    domainL2Resolvent D Ω
      (toDomainL2 D Ω (φ.oneSubLaplacianTest : H1Zero D Ω)) =
        toDomainL2 D Ω (φ : H1Zero D Ω) := by
  change toDomainL2 D Ω (domainResolvent D Ω _) = _
  rw [domainResolvent_oneSubLaplacianTest hΩ]

theorem domainL2Resolvent_pow_oneSubLaplacianTest (hΩ : IsOpen Ω)
    (m : ℕ) (φ : EnergyTest D Ω) :
    ((domainL2Resolvent D Ω) ^ m)
      (toDomainL2 D Ω (((EnergyTest.oneSubLaplacianTest)^[m]) φ : H1Zero D Ω)) =
        toDomainL2 D Ω (φ : H1Zero D Ω) := by
  induction m generalizing φ with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', Function.iterate_succ_apply, mul_apply_eq_comp,
      ih, domainL2Resolvent_oneSubLaplacianTest hΩ]

theorem heatSemigroup_domainL2Resolvent_commute (D : LeviCivitaData g)
    (hn : 0 < n) (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω)) (t : ℝ≥0) :
    Commute (heatSemigroup D Ω hn hΩ hc t) (domainL2Resolvent D Ω) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (eigenbasis D Ω hn hΩ hc).repr.injective
  ext i
  simp only [mul_apply_eq_comp, heatSemigroup,
    Poincare.Analysis.Dirichlet.Spectral.heat_repr,
    domainL2Resolvent_repr D Ω hn hΩ hc]
  ring

theorem heatSemigroup_domainL2Resolvent_pow (D : LeviCivitaData g)
    (hn : 0 < n) (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))
    (t : ℝ≥0) (m : ℕ) (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :
    heatSemigroup D Ω hn hΩ hc t (((domainL2Resolvent D Ω)^m) f) =
      ((domainL2Resolvent D Ω)^m) (heatSemigroup D Ω hn hΩ hc t f) :=
  DFunLike.congr_fun ((heatSemigroup_domainL2Resolvent_commute D hn hΩ hc t).pow_right m).eq f

end PoincareConjecture.LeviCivitaData.Dirichlet

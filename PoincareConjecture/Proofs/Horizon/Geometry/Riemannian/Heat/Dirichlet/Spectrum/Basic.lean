import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Spectrum.Eigenfunctions
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Compactness.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Dirichlet.SpectralBasis












set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

variable (D : LeviCivitaData g) (Ω : Set M) (hn : 0 < n)
  (hΩ : IsOpen Ω) (hc : IsCompact (closure Ω))

include hn hΩ hc

theorem isCompactOperator_toDomainL2 : IsCompactOperator (toDomainL2 D Ω) :=
  (isCompactOperator_toL2 D Ω hn hΩ hc).clm_comp
    (LpToLpRestrictCLM M ℝ ℝ g.volumeMeasure 2 Ω)

theorem isCompactOperator_domainL2Resolvent : IsCompactOperator (domainL2Resolvent D Ω) :=
  (isCompactOperator_toDomainL2 D Ω hn hΩ hc).comp_clm (domainResolvent D Ω)


abbrev EigenIndex := Poincare.Analysis.Dirichlet.CompactSpectral.BasisIndex (domainL2Resolvent D Ω)


def eigenbasis : HilbertBasis (EigenIndex D Ω) ℝ (Lp ℝ 2 (g.volumeMeasure.restrict Ω)) :=
  Poincare.Analysis.Dirichlet.CompactSpectral.hilbertBasis (domainL2Resolvent D Ω)
    (isCompactOperator_domainL2Resolvent D Ω hn hΩ hc)
    domainL2Resolvent_isSelfAdjoint (domainL2Resolvent_injective hΩ hc)

theorem domainL2Resolvent_eigenbasis (i : EigenIndex D Ω) :
    domainL2Resolvent D Ω (eigenbasis D Ω hn hΩ hc i) =
      i.1.1 • eigenbasis D Ω hn hΩ hc i :=
  Poincare.Analysis.Dirichlet.CompactSpectral.apply_hilbertBasis _ _ _ _ i

theorem domainL2Resolvent_repr (f : Lp ℝ 2 (g.volumeMeasure.restrict Ω))
    (i : EigenIndex D Ω) :
    (eigenbasis D Ω hn hΩ hc).repr (domainL2Resolvent D Ω f) i =
      i.1.1 * (eigenbasis D Ω hn hΩ hc).repr f i := by
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    ← domainL2Resolvent_isSelfAdjoint.isSymmetric.apply_clm,
    domainL2Resolvent_eigenbasis, real_inner_smul_left]


def eigenvalue (i : EigenIndex D Ω) : ℝ := (1 - i.1.1) / i.1.1

omit hn hΩ hc in
theorem resolvent_eigenvalue_mul_one_add (i : EigenIndex D Ω) :
    i.1.1 * (1 + eigenvalue D Ω i) = 1 := by
  dsimp [eigenvalue]
  field_simp [i.1.2.1]
  ring

theorem eigenvalue_nonneg (i : EigenIndex D Ω) : 0 ≤ eigenvalue D Ω i := by
  have hne := (eigenbasis D Ω hn hΩ hc).orthonormal.ne_zero i
  have he := domainL2Resolvent_eigenbasis D Ω hn hΩ hc i
  exact div_nonneg (sub_nonneg.mpr (domainResolvent_eigenvalue_le_one hne he))
    (domainResolvent_eigenvalue_pos hΩ hc hne he).le


def energyEigenfunction (i : EigenIndex D Ω) : H1Zero D Ω :=
  (i.1.1)⁻¹ • domainResolvent D Ω (eigenbasis D Ω hn hΩ hc i)

theorem toDomainL2_energyEigenfunction (i : EigenIndex D Ω) :
    toDomainL2 D Ω (energyEigenfunction D Ω hn hΩ hc i) = eigenbasis D Ω hn hΩ hc i :=
  domainResolvent_lift_toDomainL2 i.1.2.1 (domainL2Resolvent_eigenbasis D Ω hn hΩ hc i)

theorem energyEigenfunction_equation (i : EigenIndex D Ω) (v : H1Zero D Ω) :
    ⟪energyEigenfunction D Ω hn hΩ hc i, v⟫_ℝ =
      (1 + eigenvalue D Ω i) *
        ⟪toL2 D Ω (energyEigenfunction D Ω hn hΩ hc i), toL2 D Ω v⟫_ℝ :=
  domainResolvent_lift_weak_equation hΩ.measurableSet i.1.2.1
    (domainL2Resolvent_eigenbasis D Ω hn hΩ hc i) v

end PoincareConjecture.LeviCivitaData.Dirichlet

import PoincareConjecture.Proofs.M30.Thm11_1.ControlledCylinders
import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M13.ContractionTransport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M30

theorem scaled_terminal_curvatureTensorNorm (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (x : ((S.flow k).slice (S.base k).1).carrier) :
    (RiemannianMetric.leviCivitaData
      (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
        (S.scale k) (S.base_scalar_pos k))).curvatureTensorNorm x =
      (S.flow k).curvatureNorm ⟨(S.base k).1, x⟩ / S.scale k := by
  exact M13.homothety_curvatureTensorNorm_eq ((S.flow k).metric (S.base k).1)
    (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k))
    (Diffeomorph.refl (𝓡 3) ((S.flow k).slice (S.base k).1).carrier ∞)
    (S.scale k) (S.base_scalar_pos k)
    (M13.identity_metricHomothety ((S.flow k).metric (S.base k).1)
      (S.scale k) (S.base_scalar_pos k))
    ((S.flow k).connection (S.base k).1) _ x

theorem terminal_curvature_le_of_controlledCylinder
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ} {A T B eta : ℝ}
    (E : ControlledBlowupCylinder S k A T B eta) (hT : 0 ≤ T)
    (x : ((S.flow k).slice (S.base k).1).carrier) (hx : x ∈ S.baseBall k A) :
    (RiemannianMetric.leviCivitaData
      (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
        (S.scale k) (S.base_scalar_pos k))).curvatureTensorNorm x ≤ B := by
  rw [scaled_terminal_curvatureTensorNorm]
  apply (div_le_iff₀ (S.base_scalar_pos k)).mpr
  have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨neg_nonpos.mpr hT, le_rfl⟩
  have hbound := E.curvature_bound 0 hzero x hx
  rw [E.zero_identity hzero x hx] at hbound
  exact (le_abs_self _).trans hbound

theorem eventually_terminal_curvatureTensorNorm_le
    (hC : RicciFlowCurvatureTheory.{u}) {S : GeneralizedBlowupSequence.{u}}
    {epsilon canonicalConstant kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) (A : ℝ) (hA : 0 < A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x ∈ S.baseBall k A,
      (RiemannianMetric.leviCivitaData
        (M13.scaleSmoothMetric ((S.flow k).metric (S.base k).1)
          (S.scale k) (S.base_scalar_pos k))).curvatureTensorNorm x ≤ B := by
  obtain ⟨T, hT, B, hB, hcyl⟩ :=
    exists_radius_dependent_controlled_cylinders hC H hbound A hA
  refine ⟨B, hB, ?_⟩
  filter_upwards [hcyl 1 zero_lt_one] with k hk x hx
  obtain ⟨E⟩ := hk
  exact terminal_curvature_le_of_controlledCylinder E hT.le x hx

end PoincareConjecture.M30

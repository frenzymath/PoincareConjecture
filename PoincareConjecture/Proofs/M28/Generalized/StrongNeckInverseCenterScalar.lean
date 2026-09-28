import PoincareConjecture.Proofs.M28.Generalized.StrongNeckInverseCenterChart
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M28

local notation "E3" => EuclideanSpace ℝ (Fin 3)




theorem exists_inverseStrongNeckCenterChart_scalar_lower_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
        (S : GeneralizedStrongNeck F t epsilon)
        (H : RescaledRawCylinderData (C := F.slice t)
          (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
          (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S)),
        epsilon ≤ epsilon0 →
        ∀ (M : Type v) [TopologicalSpace M]
          [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
          (gLimit : RiemannianMetric 3 M) (D : LeviCivitaData gLimit)
          {R : ℝ}, R < 1 / 8 →
          ∀ (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 (strongNeckOpen S) ∞),
            Phi.source = Metric.ball 0 R →
            Phi.target =
              ((GeneralizedStrongNeck.rescaled_half_flow S H).metric 0).ball
                (strongNeckSourceCenter S) R →
          ∀ (e : PartialDiffeomorph (𝓡 3) (𝓡 3) M (F.slice t).carrier ∞)
            (K : Set M),
            (∀ y ∈ S.carrier,
              |(S.coordinate_inverse y).2| ≤ 2 * epsilon⁻¹ / 3 →
                y ∈ e.target ∧ e.symm y ∈ K) →
          ∀ (Q Ri : ℝ), 0 < Q → 0 < Ri → Ri * (Q * S.scale ^ 2) ≤ 2 →
            (∀ x ∈ K, |F.scalar ⟨t, e x⟩ / Q - D.scalarCurvature x| ≤ 1) →
            ∀ z ∈ Metric.ball 0 R,
              Ri / 4 - 1 ≤ D.scalarCurvature (inverseStrongNeckCenterChart S Phi e z) := by
  obtain ⟨epsilon0, hpos, hsmall, hratio⟩ :=
    tube.exists_cylinder_scalar_ratio_accuracy.{u}
  refine ⟨epsilon0, hpos, hsmall, ?_⟩
  intro F t epsilon S H hepsilon M _ _ _ gLimit D R hR Phi hsource htarget
    e K hcore Q Ri hQ hRi hscale hscalar z hz
  have hepsilonSmall : epsilon ≤ (1 / 200 : ℝ) := hepsilon.trans hsmall
  have hhalf : epsilon < 1 / 2 := hepsilonSmall.trans_lt (by norm_num)
  let N := strongNeck_top S hhalf
  let Psi := inverseStrongNeckCenterChart S Phi e
  obtain ⟨_, hpoint, _, _, _, _⟩ :=
    inverseStrongNeckCenterChart_domain S H hepsilonSmall hR Phi hsource htarget e K hcore
  have hneck : F.scalar ⟨t, S.center⟩ ≤ 2 * F.scalar ⟨t, (Phi z).val⟩ :=
    hratio (F.slice t).carrier (F.metric t) (F.connection t) N hepsilon
      N.center (N.central_sphere_subset N.center_on_central_sphere)
      (Phi z).val (Phi z).property
  have hnormal : S.scale ^ 2 * F.scalar ⟨t, S.center⟩ = 1 :=
    tube.neck_normalized_scalar_center N (F.connection t)
  have hrawPositive : 0 < F.scalar ⟨t, (Phi z).val⟩ := by
    have hcenter : 0 < F.scalar ⟨t, S.center⟩ := S.scalar_center_pos
    linarith
  have hnormalized := mul_le_mul_of_nonneg_left hneck (sq_nonneg S.scale)
  rw [hnormal] at hnormalized
  let a := Q * S.scale ^ 2
  let b := F.scalar ⟨t, (Phi z).val⟩ / Q
  have hbpos : 0 < b := div_pos hrawPositive hQ
  have hab : a * b = S.scale ^ 2 * F.scalar ⟨t, (Phi z).val⟩ := by
    dsimp only [a, b]
    field_simp [hQ.ne']
  have habLower : 1 ≤ 2 * (a * b) := by
    rw [hab]
    nlinarith only [hnormalized]
  change Ri * a ≤ 2 at hscale
  have hfirst := mul_le_mul_of_nonneg_left habLower hRi.le
  have hsecond := mul_le_mul_of_nonneg_right hscale hbpos.le
  have hb : Ri / 4 ≤ b := by nlinarith only [hfirst, hsecond]
  have herr := hscalar (Psi z) (hpoint z hz).1
  rw [(hpoint z hz).2] at herr
  change |b - D.scalarCurvature (Psi z)| ≤ 1 at herr
  linarith only [hb, (abs_le.mp herr).2]

end PoincareConjecture.M28

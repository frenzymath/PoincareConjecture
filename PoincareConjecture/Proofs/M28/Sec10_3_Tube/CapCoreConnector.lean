import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CapRatio
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicCompetitors

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.CapCertificate

open M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}

theorem exists_core_connectors (N : CapCertificate g) (D : LeviCivitaData g)
    {B Q : ℝ} (hB : N.cap_constant ≤ B) (hQ : 0 < Q)
    {p : M} (hp : p ∈ N.carrier) (hQp : Q ≤ D.scalarCurvature p) :
    ∃ c ∈ N.core,
      0 < D.scalarCurvature c ∧
      D.scalarCurvature c < B * D.scalarCurvature p ∧
      D.scalarCurvature p < B * D.scalarCurvature c ∧
      (∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = c ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
        MapsTo γ (Icc (0 : ℝ) 1) N.carrier ∧
        g.pathELength γ 0 1 < ENNReal.ofReal (B * Q ^ (-1 / 2 : ℝ))) ∧
      (∃ γ : ℝ → M, γ 0 = c ∧ γ 1 = p ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1) ∧
        MapsTo γ (Icc (0 : ℝ) 1) N.carrier ∧
        g.pathELength γ 0 1 < ENNReal.ofReal (B * Q ^ (-1 / 2 : ℝ))) := by
  obtain ⟨c, hc⟩ := N.core_nonempty
  have hcN := N.core_subset_carrier_m28 hc
  obtain ⟨bound, _, hratio⟩ := N.scalar_ratio
  have hbounded : BddAbove (range (fun z : N.carrier =>
      N.connection.scalarCurvature z.1)) := by
    refine ⟨bound * N.connection.scalarCurvature p, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hratio p hp z.1 z.2
  have hpSup : D.scalarCurvature p ≤
      scalarCurvatureSupOn g N.connection N.carrier := by
    rw [← N.connection.scalarCurvature_eq_m28 D p]
    exact le_csSup hbounded ⟨⟨p, hp⟩, rfl⟩
  have hpower := Real.rpow_le_rpow_of_nonpos hQ (hQp.trans hpSup)
    (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
  have hceiling :
      ENNReal.ofReal (N.cap_constant *
        scalarCurvatureSupOn g N.connection N.carrier ^ (-1 / 2 : ℝ)) ≤
      ENNReal.ofReal (B * Q ^ (-1 / 2 : ℝ)) := by
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left hpower N.cap_constant_pos.le).trans
      (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hQ.le _))
  have hdiam : intrinsicDiameter g N.carrier <
      ENNReal.ofReal (B * Q ^ (-1 / 2 : ℝ)) :=
    N.intrinsic_diameter_bound.trans_le hceiling
  have hpc : intrinsicEDist g N.carrier p c ≤ intrinsicDiameter g N.carrier :=
    le_sSup ⟨(⟨p, hp⟩, ⟨c, hcN⟩), rfl⟩
  have hcp : intrinsicEDist g N.carrier c p ≤ intrinsicDiameter g N.carrier :=
    le_sSup ⟨(⟨c, hcN⟩, ⟨p, hp⟩), rfl⟩
  exact ⟨c, hc, N.scalar_pos_of_connection D hcN,
    N.scalar_lt_mul D hB hp hcN, N.scalar_lt_mul D hB hcN hp,
    exists_intrinsic_competitor g (hpc.trans_lt hdiam),
    exists_intrinsic_competitor g (hcp.trans_lt hdiam)⟩

end PoincareConjecture.CapCertificate

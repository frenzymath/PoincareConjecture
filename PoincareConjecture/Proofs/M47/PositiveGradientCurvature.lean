import PoincareConjecture.Proofs.M47.PositivePinching
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Curvature.ThreeDimensional










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}





theorem curvature_norm_le_scalar_of_sectional_nonneg (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (x : M)
    (hsection : ∀ u v : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair g x u v → 0 ≤ D.curvatureTensor x u v u v) :
    D.curvatureTensorNorm x ≤ D.scalarCurvature x := by
  let S : Set ℝ := {k | ∃ u v : TangentSpace (𝓡 3) x,
    LeviCivitaData.IsOrthonormalPair g x u v ∧ k = D.curvatureTensor x u v u v}
  have hleast : 0 ≤ D.leastSectionalCurvature x := by
    change 0 ≤ sInf S
    by_cases hS : S.Nonempty
    · apply le_csInf hS
      rintro k ⟨u, v, huv, rfl⟩
      exact hsection u v huv
    · rw [Set.not_nonempty_iff_eq_empty.mp hS, Real.sInf_empty]
  obtain ⟨a, b, c, hab, hbc, hmin, hscalar, hnorm⟩ :=
    D.three_dimensional_curvature_spectrum hD x
  have hc : 0 ≤ c := hmin ▸ hleast
  have hb : 0 ≤ b := hc.trans hbc
  have ha : 0 ≤ a := hb.trans hab
  have hR : 0 ≤ D.scalarCurvature x := by rw [hscalar]; positivity
  have hN : 0 ≤ D.curvatureTensorNorm x := Real.sqrt_nonneg _
  apply (sq_le_sq₀ hN hR).mp
  rw [hnorm, hscalar]
  nlinarith only [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]




theorem curvature_norm_le_scalar_on_positive_flow
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hC : RicciFlowCurvatureTheory.{u}) {T : ℝ} (hT : 0 < T)
    (F : RicciFlow 3 M (Ico 0 T))
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
        0 < (F.connection 0).sectionalCurvature x v w) :
    ∀ t ∈ Ico 0 T, ∀ x : M,
      (F.connection t).curvatureTensorNorm x ≤ (F.connection t).scalarCurvature x := by
  obtain ⟨m, hm, hinit⟩ := PoincareConjecture.Proofs.M46.exists_initial_sectional_lower
    F ⟨le_rfl, hT⟩ isClosed_univ (fun x _ => hpos x)
  intro t ht x
  have hpres : ∀ u v : TangentSpace (𝓡 3) x,
      m * M04.metricGram (F.metric t) x u v ≤ (F.connection t).curvatureTensor x u v u v := by
    rcases eq_or_lt_of_le ht.1 with heq | htime
    · subst t
      exact hinit x (mem_univ x)
    · exact PoincareConjecture.Proofs.M46.sectional_lower_on_closed_interval F htime hm.le
        (fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩) isOpen_univ isClosed_univ
        hinit t ⟨ht.1, le_rfl⟩ x (mem_univ x)
  apply curvature_norm_le_scalar_of_sectional_nonneg (F.connection t)
    (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x
  intro u v huv
  have h := hpres u v
  have hmcurv : m ≤ (F.connection t).curvatureTensor x u v u v := by
    simpa only [M04.metricGram, huv.1, huv.2.1, huv.2.2,
      one_mul, zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_one] using h
  exact hm.le.trans hmcurv

end PoincareConjecture.M47Positive

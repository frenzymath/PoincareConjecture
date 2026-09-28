import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65Edist_le_of_tangentNorm_le (g h : RiemannianMetric n M)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x), h.tangentNorm x v ≤ C * g.tangentNorm x v)
    (x y : M) : h.edist x y ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdiv : h.edist x y / ENNReal.ofReal C ≤ g.edist x y := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro R hR
    obtain ⟨gamma, h0, h1, hgamma, hlength⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hR
    have hcompare := RiemannianMetric.pathELength_le_of_tangentNorm_le
      g h gamma 0 1 C hC.le (fun r _ => hbound (gamma r))
    have hdist : h.edist x y ≤ h.pathELength gamma 0 1 := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨h.toRiemannianMetric⟩
      exact Manifold.riemannianEDist_le_pathELength hgamma h0 h1 zero_le_one
    apply (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hC))
      ENNReal.ofReal_ne_top).mpr
    exact (hdist.trans hcompare).trans
      ((mul_le_mul_right hlength.le _).trans_eq (mul_comm _ _))
  simpa only [mul_comm] using (ENNReal.div_le_iff
    (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top).mp hdiv

end PoincareConjecture

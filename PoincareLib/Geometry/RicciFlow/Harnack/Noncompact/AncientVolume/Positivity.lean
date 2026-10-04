import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Differential
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Nonflatness
import PoincareLib.Geometry.RicciFlow.Harnack.Path.Comparison
import PoincareLib.Geometry.Riemannian.Distance.Basic

/-!
# Scalar positivity for globally bounded ancient flows

Backward persistence of nonflatness supplies a positive scalar value on a
strictly earlier slice. A smooth path joins that point to any prescribed
point on the chosen slice. Integrating the bounded ancient differential
Harnack estimate along the path gives a strictly positive scalar lower bound.

Source: Morgan--Tian, Corollary 4.39, printed p. 81, and Theorem 4.40,
printed p. 82. This provides the positivity used in Kleiner--Lott
(corrected 2013), Proposition 41.13, printed p. 2678.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [SecondCountableTopology M] [NoncompactSpace M] in
private theorem exists_smooth_path_on_interval
    (g : RiemannianMetric n M) (p x : M) {a b : ℝ} (hab : a < b) :
    ∃ γ : ℝ → M, γ a = p ∧ γ b = x ∧
      ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfinite : Manifold.riemannianEDist (𝓡 n) p x < ⊤ :=
    lt_top_iff_ne_top.mpr (g.edist_ne_top p x)
  obtain ⟨γ, hγa, hγb, hγ, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hfinite hab
  exact ⟨γ, hγa, hγb, hγ⟩

/-- A nonflat globally bounded ancient flow with nonnegative curvature
operator has positive scalar curvature at every point and every time. -/
theorem scalarCurvature_pos_of_bounded_ancient
    (hC : RicciFlowCurvatureCalculus.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : M, 0 < (F.connection 0).scalarCurvature p) :
    ∀ t ≤ 0, ∀ x : M, 0 < (F.connection t).scalarCurvature x := by
  intro t ht x
  obtain ⟨p, hp⟩ := F.scalarCurvature_positive_somewhere_of_bounded_ancient
    hC hcomplete hoperator hK hbound hnonflat (t - 1) (by linarith)
  obtain ⟨γ, hγa, hγb, hγ⟩ :=
    exists_smooth_path_on_interval (F.metric t) p x (a := t - 1) (b := t) (by linarith)
  have hi := Poincare.Geometry.RicciFlow.Harnack.ancient_integrated_of_differential
    hC F hoperator (F.ancient_differential_of_bounded_ancient hC hcomplete hoperator hK hbound)
    (by linarith : t - 1 < t) ht γ hγ.contMDiffOn hγa hγb
  exact (mul_pos hp (Real.exp_pos _)).trans_le hi

end PoincareMT.RicciFlow

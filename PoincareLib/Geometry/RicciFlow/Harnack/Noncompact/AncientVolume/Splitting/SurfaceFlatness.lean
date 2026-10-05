import PoincareLib.Geometry.Riemannian.Surface.Curvature
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.HomotheticField
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Positivity

/-!
# The surface obstruction to a nonflat line splitting

A nonzero vector in the curvature kernel of a surface forces the scalar
curvature, hence the entire curvature tensor, to vanish. This supplies the
pointwise algebra in the dimension-two base case of Kleiner--Lott,
Proposition 41.13, corrected 2013 journal version, printed p. 2678.
The geometric production of a parallel line direction remains separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT.LeviCivitaData

variable {S : Type u} [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {g : RiemannianMetric 2 S}

/-- A nonzero curvature-kernel vector forces zero scalar curvature in dimension two. -/
theorem scalarCurvature_eq_zero_of_curvature_null_vector
    (D : LeviCivitaData g) (x : S) (v : TangentSpace (𝓡 2) x)
    (hv : v ≠ 0)
    (hnull : ∀ a b : TangentSpace (𝓡 2) x, D.curvature x a b v = 0) :
    D.scalarCurvature x = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : S → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hd : Module.finrank ℝ (TangentSpace (𝓡 2) x) = 2 := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 2)), finrank_euclideanSpace]
    simp
  let b : OrthonormalBasis (Fin 2) ℝ (TangentSpace (𝓡 2) x) :=
    (g.orthonormalBasis x).reindex (finCongr hd)
  have hb (i : Fin 2) : g.inner x (b i) (b i) = 1 := by
    exact b.inner_eq_ite i i |>.trans (if_pos rfl)
  have hnorm : g.inner x v v =
      (g.inner x (b 0) v) ^ 2 + (g.inner x (b 1) v) ^ 2 := by
    change inner ℝ v v = (inner ℝ (b 0) v) ^ 2 + (inner ℝ (b 1) v) ^ 2
    simpa only [Fin.sum_univ_two, real_inner_comm v (b 0),
      real_inner_comm v (b 1), pow_two] using (b.sum_inner_mul_inner v v).symm
  have hzero (i : Fin 2) :
      D.scalarCurvature x / 2 * (g.inner x v v - (g.inner x (b i) v) ^ 2) = 0 := by
    have h : D.curvatureTensor x (b i) v (b i) v = 0 := by
      simp only [curvatureTensor, hnull, map_zero, zero_apply]
    rw [D.curvatureTensor_eq_half_scalarCurvature, hb, one_mul,
      g.symm x v (b i), ← pow_two] at h
    exact h
  have hprod : D.scalarCurvature x * g.inner x v v = 0 := by
    have h0 := hzero 0
    have h1 := hzero 1
    rw [hnorm] at h0 h1 ⊢
    nlinarith
  exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (g.pos x v hv))

/-- The same pointwise obstruction annihilates every curvature component. -/
theorem curvatureTensor_eq_zero_of_curvature_null_vector
    (D : LeviCivitaData g) (x : S) (v : TangentSpace (𝓡 2) x)
    (hv : v ≠ 0)
    (hnull : ∀ a b : TangentSpace (𝓡 2) x, D.curvature x a b v = 0)
    (a b c d : TangentSpace (𝓡 2) x) :
    D.curvatureTensor x a b c d = 0 := by
  rw [D.curvatureTensor_eq_half_scalarCurvature,
    D.scalarCurvature_eq_zero_of_curvature_null_vector x v hv hnull]
  simp

end PoincareMT.LeviCivitaData

open Set

namespace PoincareMT.RicciFlow

/-- A nonflat bounded ancient surface cannot carry a nonzero parallel field
on any slice. This is the obstruction once a line splitting is constructed. -/
theorem parallel_field_eq_zero_of_bounded_ancient_surface
    {S : Type u} [TopologicalSpace S] [T3Space S]
    [SecondCountableTopology S] [ConnectedSpace S] [NoncompactSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 2 S (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : S, 0 < (F.connection 0).scalarCurvature p)
    {t : ℝ} (ht : t ≤ 0)
    (V : (x : S) → TangentSpace (𝓡 2) x)
    (hVsmooth : ContMDiff (𝓡 2) ((𝓡 2).prod (𝓡 2)) ∞ (T% V))
    (hparallel : ∀ x, ∀ v : TangentSpace (𝓡 2) x, (F.connection t).connection V x v = 0)
    (x : S) : V x = 0 := by
  by_contra hv
  have hnull := (F.connection t).curvature_eq_zero_of_constant_covariantDerivative
    (hC.tensor_calculus 2 S (F.metric t) (F.connection t)) V hVsmooth 0
    (by simpa only [zero_smul] using hparallel)
  have hzero := (F.connection t).scalarCurvature_eq_zero_of_curvature_null_vector
    x (V x) hv (hnull x)
  have hpos := F.scalarCurvature_pos_of_bounded_ancient
    hC hcomplete hoperator hK hbound hnonflat t ht x
  linarith

end PoincareMT.RicciFlow

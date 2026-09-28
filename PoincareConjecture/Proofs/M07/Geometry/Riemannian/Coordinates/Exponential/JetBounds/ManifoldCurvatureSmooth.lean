import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.TensorPullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalSecondBianchi
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Bundle VectorField
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem exists_chart_metric (g : RiemannianMetric n M) (x : M) :
    ∃ (gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (_D : LeviCivitaData gE),
      ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x), ∀ u v : EuclideanSpace ℝ (Fin n),
        gE.inner y u v = g.inner ((extChartAt (𝓡 n) x).symm y)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y u)
          (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y v) := by
  let c := extChartAt (𝓡 n) x
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨gE, DE, V, hVo, hpV, _, heq⟩ :=
    RiemannianMetric.exists_local_realization (isOpen_extChartAt_target x)
      (mem_extChartAt_target x) (g.pullbackCoefficients c.symm)
      (fun y hy => (g.contDiffAt_pullbackCoefficients (hc y hy)).contDiffWithinAt)
      (fun y _ u v => g.symm (c.symm y) _ _)
      (fun y hy v hv => by
        apply g.pos (c.symm y)
        intro hzero
        apply hv
        apply (hi y hy).injective
        rw [map_zero]
        convert! hzero using 1)
  refine ⟨gE, DE, ?_⟩
  filter_upwards [hVo.mem_nhds hpV] with y hy u v
  exact congrArg (fun B => B u v) (heq y hy)

theorem curvatureOnFields_eq_curvature_manifold (D : LeviCivitaData g)
    {X Y Z : (y : M) → TangentSpace (𝓡 n) y} {x : M}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) x) :
    D.curvatureOnFields X Y Z x = D.curvature x (X x) (Y x) (Z x) := by
  let c := extChartAt (𝓡 n) x
  let p := c x
  have hp : c.symm p = x := c.left_inv (mem_extChartAt_source x)
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm p :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hi : ∀ᶠ y in 𝓝 p, (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x)] with y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨gE, DE, hE⟩ := exists_chart_metric g x
  have hX' : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% X) (c.symm p) := hp.symm ▸ hX
  have hY' : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y) (c.symm p) := hp.symm ▸ hY
  have hZ' : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Z) (c.symm p) := hp.symm ▸ hZ
  have hf := DE.curvatureOnFields_mpullback D hc hi hE hX' hY' hZ'
  rw [DE.curvatureOnFields_eq_curvature_euclidean_of_contMDiffAt
    (hX'.mpullback_vectorField_preimage hc hi.self_of_nhds (by simp))
    (hY'.mpullback_vectorField_preimage hc hi.self_of_nhds (by simp))
    (hZ'.mpullback_vectorField_preimage hc hi.self_of_nhds (by simp)),
    DE.curvature_eq_pullback_euclidean D hc hi hE] at hf
  simp only [mpullback_apply, hi.self_of_nhds.self_apply_inverse] at hf
  have h := congrArg (mfderiv (𝓡 n) (𝓡 n) c.symm p) hf
  simp only [hi.self_of_nhds.self_apply_inverse] at h
  exact hp ▸ h.symm

theorem riemannEvaluation_isSmooth_manifold (D : LeviCivitaData g) :
    IsSmoothCovariantTensor D.riemannEvaluation := by
  constructor
  · intro x
    let A : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace (𝓡 n) x) ℝ :=
      { toFun := D.riemannEvaluation x
        map_update_add' := by
          classical
          intro _ v i a b
          fin_cases i
          · simpa [riemannEvaluation, Function.update, Fin.ext_iff] using
              D.curvatureTensor_add_first x a b (v 1) (v 2) (v 3)
          · simpa [riemannEvaluation, Function.update, Fin.ext_iff] using
              D.curvatureTensor_add_second x (v 0) a b (v 2) (v 3)
          · simpa [riemannEvaluation, Function.update, Fin.ext_iff] using
              D.curvatureTensor_add_third x (v 0) (v 1) a (v 3) b
          · simpa [riemannEvaluation, Function.update, Fin.ext_iff] using
              D.curvatureTensor_add_last x (v 0) (v 1) (v 2) a b
        map_update_smul' := by
          classical
          intro _ v i c a
          fin_cases i
          · simpa [riemannEvaluation, Function.update, Fin.ext_iff] using
              D.curvatureTensor_smul_first x c a (v 1) (v 2) (v 3)
          · simpa [riemannEvaluation, Function.update, Fin.ext_iff] using
              D.curvatureTensor_smul_second x c (v 0) a (v 2) (v 3)
          · simpa [riemannEvaluation, Function.update, Fin.ext_iff] using
              D.curvatureTensor_smul_third x c (v 0) (v 1) a (v 3)
          · simpa [riemannEvaluation, Function.update, Fin.ext_iff] using
              D.curvatureTensor_smul_last x c (v 0) (v 1) (v 2) a }
    exact ⟨A, fun _ => rfl⟩
  · intro U hU X hX x hx
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hXi (i : Fin 4) := (hX i).contMDiffAt (hU.mem_nhds hx)
    have hc := (D.contMDiffAt_curvatureOnFields (hXi 0) (hXi 1) (hXi 3)).inner_bundle (hXi 2)
    apply ContMDiffAt.contMDiffWithinAt
    apply hc.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    have hYi (i : Fin 4) := (hX i).contMDiffAt (hU.mem_nhds hy)
    change g.inner y (D.curvature y (X 0 y) (X 1 y) (X 3 y)) (X 2 y) = _
    rw [D.curvatureOnFields_eq_curvature_manifold (hYi 0) (hYi 1) (hYi 3)]
    rfl

end PoincareConjecture.LeviCivitaData

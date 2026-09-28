import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.ScalarFlow
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.RicciPositive
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Rank

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] in
private theorem ricci_eq_of_metric_eq {g h : RiemannianMetric 3 M}
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (heq : g = h)
    (x : M) (v w : TangentSpace (𝓡 3) x) : D.ricci x v w = D'.ricci x v w := by
  subst h
  simp only [LeviCivitaData.ricci, D.horizon_curvatureTensor_eq D']

theorem scalarCurvature_pos
    (S : GradientShrinkingSolitonData 3 M) (hC : RicciFlowCurvatureTheory.{u})
    (x : M) : 0 < S.connection.scalarCurvature x := by
  obtain ⟨G⟩ := exists_shrinkingSolitonFlow S
  have hD := hC.tensor_calculus 3 M S.metric S.connection
  have hsame (y : M) (a b : TangentSpace (𝓡 3) y) :
      (G.flow.connection (-1)).ricci y a b = S.connection.ricci y a b :=
    ricci_eq_of_metric_eq _ _ G.at_minus_one y a b
  have hnull (y : M) :
      RicciFlow.Splitting.ricciNullity (G.flow.connection (-1)) y =
        RicciFlow.Splitting.ricciNullity S.connection y := by
    have hker : RicciFlow.Splitting.ricciKernel (G.flow.connection (-1)) y =
        RicciFlow.Splitting.ricciKernel S.connection y := by
      ext v
      simp only [RicciFlow.Splitting.mem_ricciKernel, hsame]
    exact congrArg (fun K : Submodule ℝ (TangentSpace (𝓡 3) y) =>
      Module.finrank ℝ K) hker
  obtain ⟨p, hp⟩ := S.nonflat
  have hupper := S.connection.ricciNullity_le_one_of_nonflat hD p
    (S.nonnegative_curvature p) hp
  let F := Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.flow
    (show Icc (-2 : ℝ) (-1) ⊆ Iio 0 from fun _ hs => lt_of_le_of_lt hs.2 (by norm_num))
    ordConnected_Icc ⟨-2, by simp, -1, by simp, by norm_num⟩
  have hdim := RicciFlow.Splitting.ricciNullity_eq_on_positive_slice hC
    (by norm_num : (-2 : ℝ) < -1) F
    (fun t ht => G.nonnegativeSectionalCurvature (lt_of_le_of_lt ht.2 (by norm_num)))
    (show (-1 : ℝ) ∈ Ioc (-2) (-1) by norm_num) x p
  change RicciFlow.Splitting.ricciNullity (G.flow.connection (-1)) x =
    RicciFlow.Splitting.ricciNullity (G.flow.connection (-1)) p at hdim
  rw [hnull, hnull] at hdim
  have hRic (v : TangentSpace (𝓡 3) x) :=
    S.connection.ricci_bounds_of_nonnegative_curvatureOperator hD x
      (S.nonnegative_curvature x) v
  have hnonneg : 0 ≤ S.connection.scalarCurvature x :=
    Finset.sum_nonneg (fun i _ => (hRic (S.metric.orthonormalBasis x i)).1)
  by_contra hpos
  have hzero : S.connection.scalarCurvature x = 0 :=
    le_antisymm (le_of_not_gt hpos) hnonneg
  have hRiczero (v : TangentSpace (𝓡 3) x) : S.connection.ricci x v v = 0 := by
    have hb := (hRic v).2
    rw [hzero, zero_mul] at hb
    exact le_antisymm hb (hRic v).1
  have hkernel : RicciFlow.Splitting.ricciKernel S.connection x = ⊤ := by
    apply top_unique
    intro v _
    apply (RicciFlow.Splitting.mem_ricciKernel _ _ _).mpr
    exact RicciFlow.Splitting.ricci_eq_zero_of_nonneg_of_self_eq_zero
      S.connection hD x (fun w => (hRic w).1) (hRiczero v)
  have hdimx : RicciFlow.Splitting.ricciNullity S.connection x = 3 := by
    unfold RicciFlow.Splitting.ricciNullity
    rw [hkernel]
    simp [TangentSpace]
  omega

theorem exists_uniform_positive_scalar_lower_bound
    (S : GradientShrinkingSolitonData 3 M) (hC : RicciFlowCurvatureTheory.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, c ≤ S.connection.scalarCurvature x :=
  S.exists_scalar_positive_global_lower_bound (hC.tensor_calculus 3 M S.metric S.connection)
    (S.scalarCurvature_pos hC)

theorem not_bddAbove_distance_sq_mul_scalarCurvature
    (S : GradientShrinkingSolitonData 3 M) (hC : RicciFlowCurvatureTheory.{u})
    (hM : ¬ CompactSpace M) (p : M) :
    ¬ BddAbove (range (fun x =>
      (S.metric.edist p x).toReal ^ 2 * S.connection.scalarCurvature x)) := by
  obtain ⟨c, hc, hlower⟩ := S.exists_uniform_positive_scalar_lower_bound hC
  rintro ⟨B, hB⟩
  have hdist (x : M) : (S.metric.edist p x).toReal ≤ |B| / c + 1 := by
    have hb := hB (mem_range_self x)
    have hprod := mul_le_mul_of_nonneg_left (hlower x)
      (sq_nonneg (S.metric.edist p x).toReal)
    have hsq : (S.metric.edist p x).toReal ^ 2 ≤ |B| / c := by
      apply (le_div_iff₀ hc).mpr
      exact hprod.trans (hb.trans (le_abs_self B))
    nlinarith [sq_nonneg ((S.metric.edist p x).toReal - 1 / 2)]
  have hball : {x : M | S.metric.edist p x ≤ ENNReal.ofReal (|B| / c + 1)} = univ := by
    apply eq_univ_of_forall
    intro x
    change S.metric.edist p x ≤ ENNReal.ofReal (|B| / c + 1)
    rw [← ENNReal.ofReal_toReal (S.metric.edist_ne_top p x)]
    exact ENNReal.ofReal_le_ofReal (hdist x)
  apply hM
  exact isCompact_univ_iff.mp (hball ▸
    S.metric.isCompact_closedBall_of_metricComplete S.complete p (|B| / c + 1))

end PoincareConjecture.GradientShrinkingSolitonData

import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.LowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Curvature.Bound







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology BigOperators

private theorem continuousAt_multilinear_of_basis
    {X V ι κ : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis ι ℝ V)
    (A : X → MultilinearMap ℝ (fun _ : κ => V) ℝ)
    {x : X} {v : X → κ → V}
    (hA : ∀ p : κ → ι, ContinuousAt (fun y => A y (fun j => b (p j))) x)
    (hv : ContinuousAt v x) : ContinuousAt (fun y => A y (v y)) x := by
  classical
  have heq (y : X) : A y (v y) = ∑ p : κ → ι,
      (∏ j, b.repr (v y j) (p j)) * A y (fun j => b (p j)) := by
    conv_lhs => rw [show v y = (fun j => ∑ i, b.repr (v y j) i • b i) by
      funext j
      exact (b.sum_repr (v y j)).symm]
    rw [(A y).map_sum]
    simp only [MultilinearMap.map_smul_univ, smul_eq_mul]
  simp_rw [heq]
  apply tendsto_finsetSum
  intro p _
  apply ContinuousAt.mul _ (hA p)
  apply tendsto_finsetProd
  intro j _
  simp only [b.repr_apply_apply]
  exact continuousAt_const.inner ((continuous_apply j).continuousAt.comp hv)

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

set_option maxHeartbeats 800000 in


theorem exists_pos_le_curvatureTensor_orthonormal
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ∃ κ > 0, ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → κ ≤ D.curvatureTensor x u v u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let K : Set (TangentSpace (𝓡 n) x × TangentSpace (𝓡 n) x) :=
    {z | inner ℝ z.1 z.1 = 1 ∧ inner ℝ z.2 z.2 = 1 ∧ inner ℝ z.1 z.2 = 0}
  have hclosed : IsClosed K :=
    ((isClosed_eq (continuous_fst.inner continuous_fst) continuous_const).inter
      ((isClosed_eq (continuous_snd.inner continuous_snd) continuous_const).inter
        (isClosed_eq (continuous_fst.inner continuous_snd) continuous_const)))
  have hcompact : IsCompact K := by
    apply ((isCompact_closedBall (0 : TangentSpace (𝓡 n) x) 1).prod
      (isCompact_closedBall (0 : TangentSpace (𝓡 n) x) 1)).of_isClosed_subset hclosed
    intro z hz
    have hu : ‖z.1‖ ^ 2 = 1 := (real_inner_self_eq_norm_sq z.1).symm.trans hz.1
    have hv : ‖z.2‖ ^ 2 = 1 := (real_inner_self_eq_norm_sq z.2).symm.trans hz.2.1
    simp only [mem_prod, Metric.mem_closedBall, dist_zero_right]
    constructor <;> nlinarith [norm_nonneg z.1, norm_nonneg z.2]
  obtain ⟨A, hA⟩ := D.curvatureTensor_multilinear x
  have hcont : Continuous (fun z : TangentSpace (𝓡 n) x × TangentSpace (𝓡 n) x =>
      D.curvatureTensor x z.1 z.2 z.1 z.2) := by
    have htuple : Continuous (fun z : TangentSpace (𝓡 n) x × TangentSpace (𝓡 n) x =>
        ![z.1, z.2, z.1, z.2]) := by
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop
    apply continuous_iff_continuousAt.mpr
    intro z
    have hc := continuousAt_multilinear_of_basis (g.orthonormalBasis x)
      (fun _ : TangentSpace (𝓡 n) x × TangentSpace (𝓡 n) x => A)
      (fun _ => continuousAt_const) (htuple.continuousAt (x := z))
    simpa [← hA, riemannEvaluation] using hc
  have hpos (z : TangentSpace (𝓡 n) x × TangentSpace (𝓡 n) x) (hz : z ∈ K) :
      0 < D.curvatureTensor x z.1 z.2 z.1 z.2 := by
    have h := hsec z.1 z.2 hz.1 hz.2.1 hz.2.2
    have hu : g.inner x z.1 z.1 = 1 := hz.1
    have hv : g.inner x z.2 z.2 = 1 := hz.2.1
    have huv : g.inner x z.1 z.2 = 0 := hz.2.2
    simpa [sectionalCurvature, hu, hv, huv] using h
  obtain ⟨κ, hκ, hbound⟩ := hcompact.exists_forall_le' hcont.continuousOn hpos
  exact ⟨κ, hκ, fun u v hu hv huv => hbound (u, v) ⟨hu, hv, huv⟩⟩

set_option maxHeartbeats 1000000 in


theorem exists_pos_eventually_le_curvatureTensor_orthonormal
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ∃ κ > 0, ∀ᶠ y in 𝓝 x, ∀ u v, g.inner y u u = 1 →
      g.inner y v v = 1 → g.inner y u v = 0 →
      κ ≤ D.curvatureTensor y u v u v := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) x) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let L (y : M) : TangentSpace (𝓡 n) y →L[ℝ] TangentSpace (𝓡 n) x :=
    (e.symmL ℝ x).comp (e.continuousLinearMapAt ℝ y)
  let K (y : M) : TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) y :=
    (e.symmL ℝ y).comp (e.continuousLinearMapAt ℝ x)
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  have hKx (u : TangentSpace (𝓡 n) x) : K x u = u := by
    simp only [K, ContinuousLinearMap.comp_apply, e.symmL_continuousLinearMapAt hx]
  have hKL (y : M) (hy : y ∈ e.baseSet) (u : TangentSpace (𝓡 n) y) :
      K y (L y u) = u := by
    simp only [K, L, ContinuousLinearMap.comp_apply,
      e.continuousLinearMapAt_symmL hx, e.symmL_continuousLinearMapAt hy]
  have hKe (y : M) (hy : y ∈ e.baseSet) (u : TangentSpace (𝓡 n) x) :
      K y u = FiberBundle.extend (EuclideanSpace ℝ (Fin n)) u y := by
    simp only [K, ContinuousLinearMap.comp_apply, FiberBundle.extend]
    rw [e.symmL_apply hy, e.continuousLinearMapAt_apply_of_mem ℝ hx]
  have hKc (u : TangentSpace (𝓡 n) x) : ContinuousAt
      (fun z : M × TangentSpace (𝓡 n) x =>
        TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) z.1 (K z.1 z.2)) (x, u) := by
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuousAt_fst, ?_⟩
    have heq : (fun z : M × TangentSpace (𝓡 n) x =>
        (e (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) z.1 (K z.1 z.2))).2) =ᶠ[𝓝 (x, u)]
        (fun z => e.continuousLinearMapAt ℝ x z.2) := by
      filter_upwards [continuousAt_fst.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)] with z hz
      rw [← e.continuousLinearMapAt_apply_of_mem ℝ hz]
      simp only [K, ContinuousLinearMap.comp_apply, e.continuousLinearMapAt_symmL hz]
    exact ((e.continuousLinearMapAt ℝ x).continuous.continuousAt.comp
      continuousAt_snd).congr_of_eventuallyEq heq
  let T := TangentSpace (𝓡 n) x × TangentSpace (𝓡 n) x
  let r (y : M) (z : T) := D.curvatureTensor y (K y z.1) (K y z.2) (K y z.1) (K y z.2)
  have hrc (z : T) : ContinuousAt (fun w : M × T => r w.1 w.2) (x, z) := by
    choose A hA using D.curvatureTensor_multilinear
    let B (y : M) := (A y).compLinearMap (fun _ : Fin 4 => (K y).toLinearMap)
    have hcoeff (p : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
        ContinuousAt (fun y => B y (fun j => g.orthonormalBasis x (p j))) x := by
      have heq : (fun y => B y (fun j => g.orthonormalBasis x (p j))) =ᶠ[𝓝 x]
          (fun y => D.riemannEvaluation y (fun j =>
            FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (g.orthonormalBasis x (p j)) y)) := by
        filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
        simp only [B, MultilinearMap.compLinearMap_apply, ContinuousLinearMap.coe_coe,
          ← hA, hKe y hy]
      exact (normalization_continuousAt_riemannEvaluation_extend D x
        (fun j => g.orthonormalBasis x (p j))).congr_of_eventuallyEq heq
    have htuple : Continuous (fun w : M × T => ![w.2.1, w.2.2, w.2.1, w.2.2]) := by
      dsimp only [T]
      apply continuous_pi
      intro i
      fin_cases i <;> fun_prop
    have hcoeff' (p : Fin 4 → Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
        ContinuousAt (fun w : M × T => B w.1 (fun j => g.orthonormalBasis x (p j))) (x, z) :=
      (hcoeff p).comp_of_eq
        (show ContinuousAt (fun w : M × T => w.1) (x, z) from continuousAt_fst) rfl
    have hc := continuousAt_multilinear_of_basis (g.orthonormalBasis x)
      (fun w : M × T => B w.1) hcoeff'
      (htuple.continuousAt (x := (x, z)))
    simpa [r, B, ← hA, riemannEvaluation] using hc

  let F (y : M) (z : T) := r y z +
    (g.inner y (K y z.1) (K y z.1) - 1) ^ 2 +
    (g.inner y (K y z.2) (K y z.2) - 1) ^ 2 +
    (g.inner y (K y z.1) (K y z.2)) ^ 2
  have hFc (z : T) : ContinuousAt (fun w : M × T => F w.1 w.2) (x, z) := by
    have hpu : ContinuousAt (fun w : M × T => (w.1, w.2.1)) (x, z) :=
      continuousAt_fst.prodMk continuousAt_snd.fst
    have hpv : ContinuousAt (fun w : M × T => (w.1, w.2.2)) (x, z) :=
      continuousAt_fst.prodMk continuousAt_snd.snd
    have hu := (hKc z.1).comp_of_eq hpu rfl
    have hv := (hKc z.2).comp_of_eq hpv rfl
    exact (((hrc z).add (((hu.inner_bundle hu).sub continuousAt_const).pow 2)).add
      (((hv.inner_bundle hv).sub continuousAt_const).pow 2)).add ((hu.inner_bundle hv).pow 2)
  have hpos (z : T) : 0 < F x z := by
    have hnonneg := D.curvatureTensor_diagonal_nonneg_of_orthonormal x
      (fun u v hu hv huv => (hsec u v hu hv huv).le) z.1 z.2
    dsimp only [F, r]
    simp only [hKx]
    by_cases hu : g.inner x z.1 z.1 = 1
    · by_cases hv : g.inner x z.2 z.2 = 1
      · by_cases huv : g.inner x z.1 z.2 = 0
        · have hp := hsec z.1 z.2 hu hv huv
          have hp' : 0 < D.curvatureTensor x z.1 z.2 z.1 z.2 := by
            simpa [sectionalCurvature, hu, hv, huv] using hp
          positivity
        · nlinarith [sq_pos_of_ne_zero huv,
            sq_nonneg (g.inner x z.1 z.1 - 1), sq_nonneg (g.inner x z.2 z.2 - 1)]
      · nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hv), sq_nonneg (g.inner x z.1 z.2),
          sq_nonneg (g.inner x z.1 z.1 - 1)]
    · nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hu), sq_nonneg (g.inner x z.1 z.2),
        sq_nonneg (g.inner x z.2 z.2 - 1)]
  let C : Set T := Metric.closedBall 0 2 ×ˢ Metric.closedBall 0 2
  have hcompact : IsCompact C := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hcont : Continuous (F x) := continuous_iff_continuousAt.mpr fun z =>
    (hFc z).comp (continuousAt_const.prodMk continuousAt_id)
  obtain ⟨c, hc, hbound⟩ := hcompact.exists_forall_le' hcont.continuousOn (fun z _ => hpos z)
  have hevent : ∀ᶠ y in 𝓝 x, ∀ z ∈ C, c / 2 < F y z := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro z hz
    exact (hFc z).eventually (Ioi_mem_nhds (lt_of_lt_of_le (half_lt_self hc) (hbound z hz)))
  have hL : ∀ᶠ y in 𝓝 x, ‖L y‖ < 2 :=
    eventually_norm_symmL_trivializationAt_self_comp_lt (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) x one_lt_two
  refine ⟨c / 2, half_pos hc, ?_⟩
  filter_upwards [hevent, hL, e.open_baseSet.mem_nhds hx] with y hy hyL hybase
  intro u v hu hv huv
  have hnorm {w : TangentSpace (𝓡 n) y} (hw : g.inner y w w = 1) : ‖L y w‖ ≤ 2 := by
    have hw' : ‖w‖ = 1 := by
      have hh : ‖w‖ ^ 2 = 1 := (real_inner_self_eq_norm_sq w).symm.trans hw
      nlinarith [norm_nonneg w]
    calc
      ‖L y w‖ ≤ ‖L y‖ * ‖w‖ := (L y).le_opNorm w
      _ ≤ 2 := by rw [hw', mul_one]; exact hyL.le
  have hmem : (L y u, L y v) ∈ C := by
    change dist (L y u) 0 ≤ 2 ∧ dist (L y v) 0 ≤ 2
    simpa only [dist_zero_right] using And.intro (hnorm hu) (hnorm hv)
  have hb := hy (L y u, L y v) hmem
  simpa [F, r, hKL y hybase, hu, hv, huv] using hb.le



theorem exists_pos_eventually_curvatureTensor_diagonal_lower_bound
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ∃ κ > 0, ∀ᶠ y in 𝓝 x, ∀ u v,
      κ * (g.inner y u u * g.inner y v v - (g.inner y u v) ^ 2) ≤
        D.curvatureTensor y u v u v := by
  obtain ⟨κ, hκ, hnear⟩ := D.exists_pos_eventually_le_curvatureTensor_orthonormal x hsec
  refine ⟨κ, hκ, hnear.mono ?_⟩
  intro y hy u v
  apply D.curvatureTensor_diagonal_lower_bound_of_orthonormal y ?_ u v
  intro a b ha hb hab
  simpa [sectionalCurvature, ha, hb, hab] using hy a b ha hb hab

variable [T3Space M] [PreconnectedSpace M]



theorem exists_pos_curvatureTensor_lower_bound_on_edist_ball
    (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v) :
    ∃ κ > 0, ∃ ρ > 0, ∀ y, (g.edist y x).toReal ≤ ρ → ∀ u v,
      κ * (g.inner y u u * g.inner y v v - (g.inner y u v) ^ 2) ≤
        D.curvatureTensor y u v u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace g.edist_ne_top
  obtain ⟨κ, hκ, hnear⟩ := D.exists_pos_eventually_curvatureTensor_diagonal_lower_bound x hsec
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨κ, hκ, r / 2, half_pos hr, ?_⟩
  intro y hy u v
  exact hball (show y ∈ Metric.ball x r from hy.trans_lt (half_lt_self hr)) u v

end PoincareConjecture.LeviCivitaData

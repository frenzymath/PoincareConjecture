import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Source.Shape.Convergence
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Hessian








noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 1000000

open Set Filter PoincareConjecture
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Curvature.Hypersurface

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private theorem chart_symm_mfderiv {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M] (x : M) :
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x) =
      ContinuousLinearMap.id ℝ (E n) := by
  have he := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at he
  convert! he using 1

private theorem hessian_realized_chart
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (E n) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {gE : RiemannianMetric n (E n)} (DE : LeviCivitaData gE) (x : M)
    (hmetric : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x), ∀ a b,
      gE.inner y a b = g.inner ((extChartAt (𝓡 n) x).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y a)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y b))
    {φ : M → ℝ} (hφ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ x)
    (u v : TangentSpace (𝓡 n) x) :
    DE.hessian (φ ∘ (extChartAt (𝓡 n) x).symm) (extChartAt (𝓡 n) x x) u v =
      D.hessian φ x u v := by
  have hp := (extChartAt (𝓡 n) x).left_inv (mem_extChartAt_source x)
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) x).symm
      (extChartAt (𝓡 n) x x) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hi : ∀ᶠ y in 𝓝 (extChartAt (𝓡 n) x x),
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x)] with y hy
    exact Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm hy
  have he := DE.hessian_comp_of_metric_pullback D hc hi hmetric
    (by simpa only [hp] using hφ) u v
  rw [chart_symm_mfderiv] at he
  change DE.hessian (φ ∘ (extChartAt (𝓡 n) x).symm) (extChartAt (𝓡 n) x x) u v =
    D.hessian φ ((extChartAt (𝓡 n) x).symm (extChartAt (𝓡 n) x x)) u v at he
  erw [hp] at he
  exact he

variable {m : ℕ} {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace (E (m + 1)) L] [IsManifold (𝓡 (m + 1)) ∞ L]
  [ChartedSpace (E (m + 2)) M] [IsManifold (𝓡 (m + 2)) ∞ M]



theorem inner_chartShapeOperator_neg_levelUnitNormal
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    (D : LeviCivitaData g) {F : L → M}
    (hF : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ F) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b = g.inner (F p)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F p a)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F p b))
    {φ : M → ℝ} (hφ : ContMDiffAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ φ (F x))
    {c : ℝ} (hlevel : (φ ∘ F) =ᶠ[𝓝 x] fun _ => c)
    (u v : TangentSpace (𝓡 (m + 1)) x) :
    h.inner x (chartShapeOperator g h hF x hmetric (-D.levelUnitNormal φ (F x)) u) v =
      D.hessian φ (F x) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x u)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x v) / Real.sqrt (D.levelQ φ (F x)) := by
  let R := inducedChartRealization g h hF x hmetric
  let c₀ := extChartAt (𝓡 (m + 1)) x
  let d := extChartAt (𝓡 (m + 2)) (F x)
  let FE := immersionInCharts (m := m + 1) (n := m + 2) F x
  let q := φ ∘ d.symm
  have hp : c₀.symm (c₀ x) = x := c₀.left_inv (mem_extChartAt_source x)
  have hq : d.symm (d (F x)) = F x := d.left_inv (mem_extChartAt_source (F x))
  have hFE : FE (c₀ x) = d (F x) := by change d (F (c₀.symm (c₀ x))) = _; rw [hp]
  have hc : ContMDiffAt (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ c₀.symm (c₀ x) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hd : ContMDiffAt (𝓡 (m + 2)) (𝓡 (m + 2)) ∞ d.symm (d (F x)) :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) (F x)
      (mem_extChartAt_target (F x))).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target (F x)))
  have hFEc : ContDiffAt ℝ ∞ FE (c₀ x) :=
    (immersionInCharts_eventually_contDiffAt hF x).self_of_nhds
  have hdf : fderiv ℝ FE (c₀ x) = mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x := by
    symm
    unfold mfderiv
    simp only [(hF x).mdifferentiableAt (by simp),
      ModelWithCorners.range_eq_univ, fderivWithin_univ]
    rfl
  have hφq : ContMDiffAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ φ (d.symm (d (F x))) := by
    simpa only [hq] using hφ
  have hqc : ContDiffAt ℝ ∞ q (FE (c₀ x)) := by
    rw [hFE]
    exact contMDiffAt_iff_contDiffAt.mp (hφq.comp _ hd)
  have hcomm : (q ∘ FE) =ᶠ[𝓝 (c₀ x)] ((φ ∘ F) ∘ c₀.symm) := by
    have hn : ∀ᶠ y in 𝓝 (c₀ x), F (c₀.symm y) ∈ d.source := by
      apply (hF.continuous.continuousAt.comp hc.continuousAt).eventually
      change d.source ∈ 𝓝 (F (c₀.symm (c₀ x)))
      rw [hp]
      exact (isOpen_extChartAt_source (I := 𝓡 (m + 2)) (F x)).mem_nhds
        (mem_extChartAt_source (F x))
    filter_upwards [hn] with y hy
    exact congrArg φ (d.left_inv hy)
  have hc' : Tendsto c₀.symm (𝓝 (c₀ x)) (𝓝 x) := by
    simpa only [hp] using hc.continuousAt.tendsto
  have hlevc : (q ∘ FE) =ᶠ[𝓝 (c₀ x)] fun _ => c :=
    hcomm.trans (hlevel.comp_tendsto hc')
  have hchain := hessian_comp_eq_add_secondFundamentalForm R.D R.D' hFEc hqc u v
  rw [R.D'.hessian_eq_of_eventuallyEq hlevc] at hchain
  have hz : R.D'.hessian (fun _ : E (m + 1) => c) (c₀ x) u v = 0 := by
    simp [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields, mvfderiv_const]
  rw [hz, hFE, hdf] at hchain
  have hh := hessian_realized_chart D R.D (F x) R.ambient_metric hφ
    (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x u)
    (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x v)
  change R.D.hessian q (d (F x))
    (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x u)
    (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x v) = _ at hh
  erw [hh] at hchain
  let B := secondFundamentalForm R.D R.D' FE (c₀ x) u v
  have hdφ : fderiv ℝ q (d (F x)) B = g.inner (F x) (D.gradient φ (F x)) B := by
    rw [D.inner_gradient]
    have heφ := mfderiv_comp (d (F x))
      (hφq.mdifferentiableAt (by simp)) (hd.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at heφ
    have heB := congrArg (fun A => A B) heφ
    change fderiv ℝ q (d (F x)) B =
      mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) φ (d.symm (d (F x)))
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d (F x)) B) at heB
    rw [chart_symm_mfderiv] at heB
    change fderiv ℝ q (d (F x)) B =
      mfderiv (𝓡 (m + 2)) 𝓘(ℝ, ℝ) φ (d.symm (d (F x))) B at heB
    erw [hq] at heB
    exact heB
  change 0 = _ + fderiv ℝ q (d (F x)) B at hchain
  rw [hdφ] at hchain
  have hg0 (a b : E (m + 2)) : R.gE.inner (FE (c₀ x)) a b = g.inner (F x) a b := by
    rw [hFE, R.ambient_metric.self_of_nhds]
    change g.inner (d.symm (d (F x)))
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d (F x)) a)
      (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) d.symm (d (F x)) b) = _
    rw [hq, chart_symm_mfderiv]
    rfl
  have hh0 (a b : E (m + 1)) : R.hE.inner (c₀ x) a b = h.inner x a b := by
    rw [R.source_metric.self_of_nhds]
    change h.inner (c₀.symm (c₀ x))
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c₀.symm (c₀ x) a)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) c₀.symm (c₀ x) b) = _
    rw [hp, chart_symm_mfderiv]
    rfl
  have hs : chartShapeOperator g h hF x hmetric (-D.levelUnitNormal φ (F x)) u =
      shapeOperator R.D R.D' FE (c₀ x) (-D.levelUnitNormal φ (F x)) u := by
    unfold chartShapeOperator
    simp only [mfderiv_extChartAt_self, chart_symm_mfderiv]
    rfl
  rw [hs, ← hh0, inner_shapeOperator, hg0]
  simp only [LeviCivitaData.levelUnitNormal, map_neg, neg_apply, map_smul,
    smul_apply, smul_eq_mul]
  change -((Real.sqrt (D.levelQ φ (F x)))⁻¹ * g.inner (F x) (D.gradient φ (F x)) B) = _
  rw [show g.inner (F x) (D.gradient φ (F x)) B =
    -D.hessian φ (F x) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x u)
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x v) by linarith]
  ring



theorem chartShapeOperator_eigenvalue_mem_Ioo_of_levelShape_bounds
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    (D : LeviCivitaData g) {F : L → M}
    (hF : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ F) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b = g.inner (F p)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F p a)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F p b))
    {φ : M → ℝ} (hφ : ContMDiffAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ φ (F x))
    {c : ℝ} (hlevel : (φ ∘ F) =ᶠ[𝓝 x] fun _ => c) {a b : ℝ}
    (hshape : ∀ v : TangentSpace (𝓡 (m + 2)) (F x), v ≠ 0 →
      a * g.inner (F x) v v < D.hessian φ (F x) v v / Real.sqrt (D.levelQ φ (F x)) ∧
      D.hessian φ (F x) v v / Real.sqrt (D.levelQ φ (F x)) < b * g.inner (F x) v v)
    {κ : ℝ} (hκ : Module.End.HasEigenvalue
      (chartShapeOperator g h hF x hmetric (-D.levelUnitNormal φ (F x))) κ) :
    κ ∈ Ioo a b := by
  obtain ⟨v, hv⟩ := hκ.exists_hasEigenvector
  have hvpos := h.pos x v hv.2
  have hdv : mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x v ≠ 0 := by
    intro hzero
    have hzero' := hmetric.self_of_nhds v v
    simp only [hzero, map_zero] at hzero'
    linarith
  have hpinch := hshape (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x v) hdv
  rw [← hmetric.self_of_nhds v v] at hpinch
  have hpair := inner_chartShapeOperator_neg_levelUnitNormal g h D hF x hmetric hφ hlevel v v
  rw [hv.apply_eq_smul] at hpair
  simp only [map_smul, smul_apply, smul_eq_mul] at hpair
  rw [← hpair] at hpinch
  exact ⟨(mul_lt_mul_iff_left₀ hvpos).mp hpinch.1,
    (mul_lt_mul_iff_left₀ hvpos).mp hpinch.2⟩



theorem exists_unit_normal_chartShapeOperator_bounds_of_levelHessian
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    (D : LeviCivitaData g) {F : L → M}
    (hF : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ F) (x : L)
    (hmetric : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b = g.inner (F p)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F p a)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F p b))
    {φ : M → ℝ} (hφ : ContMDiffAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ φ (F x))
    {c : ℝ} (hlevel : (φ ∘ F) =ᶠ[𝓝 x] fun _ => c)
    (hreg : 0 < D.levelQ φ (F x)) {a b : ℝ}
    (hshape : ∀ v : TangentSpace (𝓡 (m + 2)) (F x), v ≠ 0 →
      a * g.inner (F x) v v < D.hessian φ (F x) v v / Real.sqrt (D.levelQ φ (F x)) ∧
      D.hessian φ (F x) v v / Real.sqrt (D.levelQ φ (F x)) < b * g.inner (F x) v v) :
    ∃ N : TangentSpace (𝓡 (m + 2)) (F x),
      g.inner (F x) N N = 1 ∧
      (∀ v, g.inner (F x) N (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x v) = 0) ∧
      ∀ κ, Module.End.HasEigenvalue (chartShapeOperator g h hF x hmetric N) κ → κ ∈ Ioo a b := by
  refine ⟨-D.levelUnitNormal φ (F x), ?_, ?_, ?_⟩
  · simp only [map_neg, neg_apply, neg_neg, LeviCivitaData.levelUnitNormal,
      map_smul, smul_apply, smul_eq_mul, mul_neg]
    change (Real.sqrt (D.levelQ φ (F x)))⁻¹ *
      ((Real.sqrt (D.levelQ φ (F x)))⁻¹ * D.levelQ φ (F x)) = 1
    have hs := Real.sq_sqrt hreg.le
    have hs0 := (Real.sqrt_pos.mpr hreg).ne'
    field_simp
    nlinarith
  · intro v
    have hzero : mvfderiv (𝓡 (m + 1)) (φ ∘ F) x v = 0 := by
      unfold mvfderiv
      rw [hlevel.mfderiv_eq]
      simp
    rw [mvfderiv_comp x (hφ.mdifferentiableAt (by simp))
      (hF.contMDiffAt.mdifferentiableAt (by simp))] at hzero
    simp only [ContinuousLinearMap.comp_apply] at hzero
    simp only [map_neg, neg_apply, LeviCivitaData.levelUnitNormal,
      map_smul, smul_apply, smul_eq_mul, D.inner_gradient, hzero, mul_zero, neg_zero]
  · intro κ hκ
    exact chartShapeOperator_eigenvalue_mem_Ioo_of_levelShape_bounds g h D hF x hmetric
      hφ hlevel hshape hκ

end Poincare.Geometry.Curvature.Hypersurface

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) P] [IsManifold (𝓡 n) ∞ P]
  {g : RiemannianMetric n M} {gP : RiemannianMetric n P}


theorem levelQ_comp_of_metric_pullback
    (D : LeviCivitaData g) (DP : LeviCivitaData gP) {e : M → P} {x : M}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e x)
    (hinv : (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible)
    (hmetric : ∀ a b : TangentSpace (𝓡 n) x,
      g.inner x a b = gP.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x a) (mfderiv (𝓡 n) (𝓡 n) e x b))
    {φ : P → ℝ} (hφ : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) φ (e x)) :
    D.levelQ (φ ∘ e) x = DP.levelQ φ (e x) := by
  have hg := D.gradient_comp_eq_mpullback DP he hφ hinv hmetric
  simp only [levelQ, hg, hmetric, VectorField.mpullback, hinv.self_apply_inverse]



theorem levelShape_bounds_comp_of_metric_pullback
    (D : LeviCivitaData g) (DP : LeviCivitaData gP) {e : M → P} {x : M}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b : TangentSpace (𝓡 n) y,
      g.inner y a b = gP.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y a) (mfderiv (𝓡 n) (𝓡 n) e y b))
    {φ : P → ℝ} (hφ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ (e x)) {a b : ℝ}
    (hshape : ∀ v : TangentSpace (𝓡 n) (e x), v ≠ 0 →
      a * gP.inner (e x) v v < DP.hessian φ (e x) v v / Real.sqrt (DP.levelQ φ (e x)) ∧
      DP.hessian φ (e x) v v / Real.sqrt (DP.levelQ φ (e x)) < b * gP.inner (e x) v v) :
    ∀ v : TangentSpace (𝓡 n) x, v ≠ 0 →
      a * g.inner x v v < D.hessian (φ ∘ e) x v v / Real.sqrt (D.levelQ (φ ∘ e) x) ∧
      D.hessian (φ ∘ e) x v v / Real.sqrt (D.levelQ (φ ∘ e) x) < b * g.inner x v v := by
  intro v hv
  have hdv : mfderiv (𝓡 n) (𝓡 n) e x v ≠ 0 := by
    intro hz
    exact hv (hinv.self_of_nhds.injective (hz.trans (map_zero _).symm))
  have hb := hshape (mfderiv (𝓡 n) (𝓡 n) e x v) hdv
  rw [D.hessian_comp_of_metric_pullback DP he hinv hmetric hφ,
    D.levelQ_comp_of_metric_pullback DP (he.mdifferentiableAt (by simp))
      hinv.self_of_nhds hmetric.self_of_nhds (hφ.mdifferentiableAt (by simp)),
    hmetric.self_of_nhds]
  exact hb

end PoincareConjecture.LeviCivitaData

namespace Poincare.Geometry.Curvature.Hypersurface

variable {m : ℕ} {L M P : Type*}
  [TopologicalSpace L] [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) L] [IsManifold (𝓡 (m + 1)) ∞ L]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] [IsManifold (𝓡 (m + 2)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) P] [IsManifold (𝓡 (m + 2)) ∞ P]




theorem exists_unit_normal_chartShapeOperator_bounds_of_local_metric_model
    (g : RiemannianMetric (m + 2) M) (h : RiemannianMetric (m + 1) L)
    (gP : RiemannianMetric (m + 2) P) (D : LeviCivitaData g) (DP : LeviCivitaData gP)
    {F : L → M} (hF : ContMDiff (𝓡 (m + 1)) (𝓡 (m + 2)) ∞ F) (x : L)
    (hinduced : ∀ᶠ p in 𝓝 x, ∀ a b,
      h.inner p a b = g.inner (F p)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F p a)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F p b))
    {e : M → P} (he : ContMDiffAt (𝓡 (m + 2)) (𝓡 (m + 2)) ∞ e (F x))
    (hinv : ∀ᶠ y in 𝓝 (F x), (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) e y).IsInvertible)
    (hmetric : ∀ᶠ y in 𝓝 (F x), ∀ a b : TangentSpace (𝓡 (m + 2)) y,
      g.inner y a b = gP.inner (e y)
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) e y a)
        (mfderiv (𝓡 (m + 2)) (𝓡 (m + 2)) e y b))
    {φ : P → ℝ} (hφ : ContMDiffAt (𝓡 (m + 2)) 𝓘(ℝ, ℝ) ∞ φ (e (F x)))
    {c : ℝ} (hlevel : ((φ ∘ e) ∘ F) =ᶠ[𝓝 x] fun _ => c)
    (hreg : 0 < DP.levelQ φ (e (F x))) {a b : ℝ}
    (hshape : ∀ v : TangentSpace (𝓡 (m + 2)) (e (F x)), v ≠ 0 →
      a * gP.inner (e (F x)) v v <
        DP.hessian φ (e (F x)) v v / Real.sqrt (DP.levelQ φ (e (F x))) ∧
      DP.hessian φ (e (F x)) v v / Real.sqrt (DP.levelQ φ (e (F x))) <
        b * gP.inner (e (F x)) v v) :
    ∃ N : TangentSpace (𝓡 (m + 2)) (F x),
      g.inner (F x) N N = 1 ∧
      (∀ v, g.inner (F x) N (mfderiv (𝓡 (m + 1)) (𝓡 (m + 2)) F x v) = 0) ∧
      ∀ κ, Module.End.HasEigenvalue (chartShapeOperator g h hF x hinduced N) κ → κ ∈ Ioo a b := by
  have hq := D.levelQ_comp_of_metric_pullback DP (he.mdifferentiableAt (by simp))
    hinv.self_of_nhds hmetric.self_of_nhds (hφ.mdifferentiableAt (by simp))
  exact exists_unit_normal_chartShapeOperator_bounds_of_levelHessian g h D hF x hinduced
    (hφ.comp (F x) he) hlevel (hq.symm ▸ hreg)
    (D.levelShape_bounds_comp_of_metric_pullback DP he hinv hmetric hφ hshape)

end Poincare.Geometry.Curvature.Hypersurface

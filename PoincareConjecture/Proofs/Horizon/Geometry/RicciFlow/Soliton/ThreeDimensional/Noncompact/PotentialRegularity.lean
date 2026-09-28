import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Euclidean
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Regularity.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryRicci










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle Topology
open Set Filter Bundle

noncomputable section

namespace PoincareConjecture.LeviCivitaData

private theorem contDiff_ricci_const_fields {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (D : LeviCivitaData g) (v w : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun x => D.ricci x v w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hconst (z : EuclideanSpace ℝ (Fin n)) :
      ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
        (fun y : EuclideanSpace ℝ (Fin n) =>
          TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y (E := TangentSpace (𝓡 n)) z) x := by
    rw [contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using
      (contMDiffAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := z) (x := x) (n := ∞))⟩
  have h := D.ricciEvaluation_isSmooth_manifold.contMDiffAt_apply
    (x := x) (X := ![fun _ => v, fun _ => w])
    (by intro i; fin_cases i <;> exact hconst _)
  exact contMDiffAt_iff_contDiffAt.mp h

private theorem contDiffOn_of_C2_gradient_soliton {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {lambda : ℝ}
    (hf : ContDiffOn ℝ 2 f U)
    (hsol : ∀ x ∈ U, ∀ v w,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w) :
    ContDiffOn ℝ ∞ f U := by
  have hfd : ContDiffOn ℝ ∞ (fderiv ℝ f) U := by
    rw [contDiffOn_infty]
    intro k
    induction k with
    | zero =>
      exact (hf.fderiv_of_isOpen hU (m := 1) (by norm_num)).of_le (by norm_num)
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨?_, by simp, ?_⟩
      · exact (hf.fderiv_of_isOpen hU (m := 1) (by norm_num)).differentiableOn
          (by norm_num)
      · apply contDiffOn_clm_apply.mpr
        intro v
        apply contDiffOn_clm_apply.mpr
        intro w
        have hg' := (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
        have hR' := (contDiff_ricci_const_fields D v w).of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
        have hΓ' := D.contDiff_connectionCoefficient.of_le
          (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
        have hright : ContDiffOn ℝ (k : ℕ∞ω)
            (fun x => lambda * g.euclideanCoefficients x v w - D.ricci x v w +
              fderiv ℝ f x (D.connectionCoefficient x v w)) U :=
          ((contDiffOn_const.mul ((hg'.contDiffOn.clm_apply contDiffOn_const).clm_apply
            contDiffOn_const)).sub hR'.contDiffOn).add
              (ih.clm_apply ((hΓ'.contDiffOn.clm_apply contDiffOn_const).clm_apply contDiffOn_const))
        apply hright.congr
        intro x hx
        have h := D.hessian_eq_fderiv_sub_connectionCoefficient_of_C2
          (hf.contDiffAt (hU.mem_nhds hx)) v w
        have heq := hsol x hx v w
        change fderiv ℝ (fderiv ℝ f) x v w = _
        dsimp only [RiemannianMetric.euclideanCoefficients]
        rw [h] at heq
        rw [add_comm] at heq
        exact (sub_eq_iff_eq_add.mp (eq_sub_of_add_eq heq))
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hU]
  exact ⟨hf.differentiableOn (by norm_num), hfd⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem contMDiff_of_C2_gradient_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 n) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := by
  intro p
  let c := extChartAt (𝓡 n) p
  have hc : IsOpen c.target := isOpen_extChartAt_target p
  have hpc : c p ∈ c.target := mem_extChartAt_target p
  have hcs : ContMDiffOn (𝓡 n) (𝓡 n) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm p
  have hcinv (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      (isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) (x := p) hy)
  have hpos : ∀ y ∈ c.target, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < g.pullbackCoefficients c.symm y v v := by
    intro y hy v hv
    change 0 < g.inner (c.symm y)
      (mfderiv (𝓡 n) (𝓡 n) c.symm y v) (mfderiv (𝓡 n) (𝓡 n) c.symm y v)
    apply g.pos
    intro hz
    exact hv ((hcinv y hy).injective (by simpa using hz))
  obtain ⟨gE, DE, V, hV, hpV, hVc, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hc hpc
      (g.pullbackCoefficients c.symm) (g.contDiffOn_chartCoefficients p)
      (fun y _ v w => g.symm (c.symm y) _ _) hpos
  have hfcomp : ContDiffOn ℝ 2 (f ∘ c.symm) V := by
    intro y hy
    exact ((hf (c.symm y)).comp y
      ((hcs.contMDiffAt (hc.mem_nhds (hVc hy))).of_le
        (by norm_cast : (2 : ℕ∞ω) ≤ ∞))).contDiffAt.contDiffWithinAt
  have heq (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V)
      (v w : TangentSpace (𝓡 n) y) :
      gE.inner y v w = g.inner (c.symm y)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y v) (mfderiv (𝓡 n) (𝓡 n) c.symm y w) := by
    change gE.euclideanCoefficients y v w = _
    rw [hmetric y hy]
    rfl
  have hsolcomp : ∀ y ∈ V, ∀ v w,
      DE.ricci y v w + DE.hessian (f ∘ c.symm) y v w = lambda * gE.inner y v w := by
    intro y hy v w
    rw [DE.hessian_comp_of_metric_pullback_of_C2 D
      (hcs.contMDiffAt (hc.mem_nhds (hVc hy)))
      (Filter.eventually_of_mem (hV.mem_nhds hy) fun z hz => hcinv z (hVc hz))
      (Filter.eventually_of_mem (hV.mem_nhds hy) fun z hz => heq z hz)
      (hf (c.symm y)) v w,
      DE.ricci_eq_of_local_isometry D hV (hcs.mono hVc) heq hy v w,
      hsol, ← heq y hy v w]
  have hs := contDiffOn_of_C2_gradient_soliton DE hV hfcomp hsolcomp
  rw [contMDiffAt_iff_source]
  simpa only [ModelWithCorners.range_eq_univ, contMDiffWithinAt_univ] using
    (hs.contDiffAt (hV.mem_nhds hpV)).contMDiffAt

end PoincareConjecture.LeviCivitaData

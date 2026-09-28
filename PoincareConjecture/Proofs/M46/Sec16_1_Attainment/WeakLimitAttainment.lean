import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.WeakLimitSmoothness









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



theorem gauge_smooth_primitive_path (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point)
    (hgamma : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ gamma (Icc 0 (Real.sqrt tau)))
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau)) :
    ∃ p : M14BackwardPath G T 0 tau (gamma 0) (gamma (Real.sqrt tau)),
      p.curve = (fun s => gamma (Real.sqrt s)) ∧ M14BackwardLAction G p = R.action := by
  have hsub (i : Fin R.count) : Icc (R.node i.castSucc) (R.node i.succ) ⊆ Icc 0 (Real.sqrt tau) :=
    (R.core_subset i).trans (R.big_subset i)
  have hsrc (i : Fin R.count) : MapsTo gamma
      (Icc (R.node i.castSucc) (R.node i.succ)) (R.gauge i).source :=
    fun _ hs => R.source i (R.core_subset i hs)
  let theta (i : Fin R.count) (s : ℝ) := ((R.gauge i).lift (gamma s)).1
  let alpha (i : Fin R.count) (s : ℝ) := ((R.gauge i).lift (gamma s)).2
  have hlift (i : Fin R.count) := ((R.gauge i).smooth.comp (hgamma.mono (hsub i)) (hsrc i))
  have hv (i : Fin R.count) :
      (R.velocity i : ℝ → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (Icc (R.node i.castSucc) (R.node i.succ))]
          deriv (fun s => (alpha i s).val) := by
    filter_upwards [M08.chart_primitive_ae_hasDerivAt (R.monotone (Fin.castSucc_le_succ i))
      (fun s => (alpha i s).val) (R.velocity i) (R.primitive i)] with s hs
    exact hs.deriv.symm
  obtain ⟨p, hp, haction⟩ := gauge_recovery_path hM12 htau R.node R.monotone R.first R.last
    gamma hgamma hclock rfl rfl (fun i => (R.gauge i).index) theta alpha
    (fun i => (contMDiff_fst.comp_contMDiffOn (hlift i)).of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
    (fun i => (contMDiff_snd.comp_contMDiffOn (hlift i)).of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
    (fun i s hs => ((R.gauge i).right_inv (gamma s) (hsrc i hs)).symm) R.velocity hv
  refine ⟨p, hp, haction.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  exact gaugeCylinderAction_eq (R.gauge i) gamma (hsrc i)
    (R.monotone (Fin.castSucc_le_succ i)) (R.velocity i)




theorem weak_limit_attained (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (p : ℕ → M14BackwardPath G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn (fun k r => (p k).curve (r ^ 2)) gamma atTop (Icc 0 (Real.sqrt tau)))
    {D : ℝ} (henergy : ∀ k,
      IntervalIntegrable (M14.pathSquareKinetic (p k)) volume 0 (Real.sqrt tau) ∧
      (∫ r in 0..Real.sqrt tau, M14.pathSquareKinetic (p k) r) ≤ D)
    (haction : Tendsto (fun k => M14BackwardLAction G (p k)) atTop
      (𝓝 (M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau))))) :
    M14AttainedDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau)) := by
  have hS : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hreg := weak_limit_contMDiffOn hM12 htau gamma hgamma hclock p hfinite hlim henergy haction
  obtain ⟨R, hR, _⟩ := exists_anchored_weak_minimum hM12
    (show Real.sqrt tau / 2 ∈ Ioo 0 (Real.sqrt tau) from ⟨half_pos hS, half_lt_self hS⟩)
    p gamma hgamma hlim henergy haction
  obtain ⟨q, _, hq⟩ := gauge_smooth_primitive_path hM12 htau gamma hreg hclock R
  refine ⟨q, (M14.isMinimizing_iff_action_eq_actionValue hfinite q).mpr ?_⟩
  exact hq.trans (gauge_primitive_action_eq_value hM12 htau gamma hgamma hclock R hfinite hR)

end PoincareConjecture.Proofs.M46

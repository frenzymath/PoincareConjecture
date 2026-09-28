import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.RetainedLocalFlow
import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.FiniteChartDescent
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.TimeTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

set_option synthInstance.maxHeartbeats 100000 in

set_option maxHeartbeats 800000 in

theorem exists_finite_terminal_extension_on_retained_carrier
    (hFlow : WithinBilinearFlowService.{0})
    {n : ℕ} {T τ : ℝ} (hτ : 0 < τ) (hτT : τ < T)
    {S : PointedFlowSequence n (-T / 2) (T / 2)}
    (G : PointedGeometricConvergence S)
    (Fsrc : ∀ k, RicciFlow n (S.carrier k).carrier (Icc (-T) 0))
    (hmetric : ∀ k t, (Fsrc k).metric t =
      (S.flow k).flow.metric (t + T / 2)) :
    let f := fun (q : G.limitCarrier.carrier) k
        (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
      ((Fsrc (G.subsequence k)).metric z.1).pullbackCoefficients
        ((fun y => ((G.embedding k).toFun (0, y)).2) ∘
          (extChartAt (𝓡 n) q).symm) z.2
    (∀ (q : G.limitCarrier.carrier) (x₀ : EuclideanSpace ℝ (Fin n)),
      x₀ ∈ (extChartAt (𝓡 n) q).target →
      ∃ r : ℝ, 0 < r ∧
        Metric.closedBall x₀ r ⊆ (extChartAt (𝓡 n) q).target ∧
        ∃ α : ℝ, 0 < α ∧
          (∀ᶠ k : ℕ in atTop,
            ∀ z ∈ Icc (-τ) 0 ×ˢ Metric.closedBall x₀ r,
            ∀ v : EuclideanSpace ℝ (Fin n),
              α * ‖v‖ ^ 2 ≤ f q k z v v) ∧
          (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
            ∀ z ∈ Icc (-τ) 0 ×ˢ Metric.closedBall x₀ r,
              ‖iteratedFDerivWithin ℝ m (f q k)
                (Icc (-τ) 0 ×ˢ Metric.closedBall x₀ r) z‖ ≤ C)) →
    ∃ F : RicciFlow n G.limitCarrier.carrier (Icc (-τ) 0),
      (∀ t ∈ Ico (-τ) 0,
        F.metric t = G.limitFlow.flow.metric (t + T / 2)) ∧
      ∀ (q : G.limitCarrier.carrier) (m : ℕ)
        (K : Set (ℝ × EuclideanSpace ℝ (Fin n))),
        IsCompact K → K ⊆ Icc (-τ) 0 ×ˢ (extChartAt (𝓡 n) q).target →
        TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m (f q k)
            (Icc (-τ) 0 ×ˢ (extChartAt (𝓡 n) q).target))
          (iteratedFDerivWithin ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2)
            (Icc (-τ) 0 ×ˢ (extChartAt (𝓡 n) q).target)) atTop K := by
  classical
  intro f hlocal
  have htime : -τ < 0 := by linarith
  have hclosure : closure (Ioo (-τ) (0 : ℝ)) = Icc (-τ) 0 :=
    closure_Ioo htime.ne
  have htranslate : (fun t : ℝ => t + T / 2) '' Ico (-τ) 0 ⊆
      Ioo (-T / 2) (T / 2) := by
    rintro s ⟨t, ht, rfl⟩
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnepast : (Ico (-τ) (0 : ℝ)).Nontrivial :=
    ⟨-τ, ⟨le_rfl, htime⟩, -τ / 2,
      ⟨by linarith, by linarith⟩, by linarith⟩
  have hneint : (Ioo (-τ) (0 : ℝ)).Nontrivial :=
    ⟨-τ / 2, ⟨by linarith, by linarith⟩, -τ / 3,
      ⟨by linarith, by linarith⟩, by linarith⟩
  let Fpast : RicciFlow n G.limitCarrier.carrier (Ico (-τ) 0) :=
    G.limitFlow.flow.translate (T / 2) htranslate ordConnected_Ico hnepast
  let Fint : RicciFlow n G.limitCarrier.carrier (Ioo (-τ) 0) :=
    Poincare.Geometry.RicciFlow.Harnack.restrictFlow Fpast
      (fun t ht => ⟨ht.1.le, ht.2⟩) ordConnected_Ioo hneint
  have hFpast (t : ℝ) : Fpast.metric t =
      G.limitFlow.flow.metric (t + T / 2) := rfl
  have hFint (t : ℝ) : Fint.metric t =
      G.limitFlow.flow.metric (t + T / 2) := rfl
  have hcenter (q : G.limitCarrier.carrier) :=
    hlocal q (extChartAt (𝓡 n) q q) (mem_extChartAt_target q)
  choose r hr hball α hα hellip hbounds using hcenter
  let U (q : G.limitCarrier.carrier) : Opens (EuclideanSpace ℝ (Fin n)) :=
    ⟨Metric.ball (extChartAt (𝓡 n) q q) (r q), Metric.isOpen_ball⟩
  have hchartExists (q : G.limitCarrier.carrier) :=
    exists_closed_flow_on_retained_chart hFlow hτ hτT G Fsrc hmetric
      q (extChartAt (𝓡 n) q q) (hr q) (hball q) (α q) (hα q)
      (hellip q) (hbounds q)
  choose B Fchart hB hBg hsymm hlower hFchart hjets using hchartExists
  let c (q : G.limitCarrier.carrier) : PartialDiffeomorph (𝓡 n) (𝓡 n)
      G.limitCarrier.carrier (EuclideanSpace ℝ (Fin n)) ∞ := {
    toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin n)) q).toPartialEquiv
    open_source := (chartAt (EuclideanSpace ℝ (Fin n)) q).open_source
    open_target := (chartAt (EuclideanSpace ℝ (Fin n)) q).open_target
    contMDiffOn_toFun := contMDiffOn_chart
    contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hcmap (q : G.limitCarrier.carrier) :
      ((c q).symm : EuclideanSpace ℝ (Fin n) → G.limitCarrier.carrier) =
        (extChartAt (𝓡 n) q).symm := by
    rw [extChartAt_coe_symm]
    rfl
  have hcsource (q : G.limitCarrier.carrier) :
      (c q).symm.source = (extChartAt (𝓡 n) q).target := by
    change (c q).target = _
    simp only [extChartAt_target, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ]
    rfl
  have hU (q : G.limitCarrier.carrier) :
      (U q : Set (EuclideanSpace ℝ (Fin n))) ⊆ (c q).symm.source := by
    rw [hcsource]
    exact Metric.ball_subset_closedBall.trans (hball q)
  let e (q : G.limitCarrier.carrier) : U q → G.limitCarrier.carrier :=
    fun x => (c q).symm x
  have he (q : G.limitCarrier.carrier) :
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (e q) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 n) (U q) x).comp
      (𝓡 n) G.limitCarrier.carrier ⟨(c q).symm, hU q x.property, Set.eqOn_refl _ _⟩
  have hcover (y : G.limitCarrier.carrier) : ∃ q x, e q x = y := by
    refine ⟨y, ⟨extChartAt (𝓡 n) y y, Metric.mem_ball_self (hr y)⟩, ?_⟩
    change (c y).symm (extChartAt (𝓡 n) y y) = y
    rw [hcmap]
    exact (extChartAt (𝓡 n) y).left_inv (mem_extChartAt_source y)
  have hinterior (t : ℝ) (ht : t ∈ Ioo (-τ) 0) (q : G.limitCarrier.carrier)
      (x : U q) (v w : TangentSpace (𝓡 n) x) :
      ((Fchart q).metric t).inner x v w = (Fint.metric t).inner (e q x)
        (mfderiv (𝓡 n) (𝓡 n) (e q) x v)
        (mfderiv (𝓡 n) (𝓡 n) (e q) x w) := by
    have hpoint : (t, (x : EuclideanSpace ℝ (Fin n))) ∈
        interior (Icc (-τ) 0 ×ˢ Metric.closedBall (extChartAt (𝓡 n) q q) (r q)) := by
      rw [interior_prod_eq, interior_Icc, interior_closedBall _ (hr q).ne']
      exact ⟨ht, x.property⟩
    have hvalue : B q (t, (x : EuclideanSpace ℝ (Fin n))) =
        (G.limitFlow.flow.metric (t + T / 2)).pullbackCoefficients
          (extChartAt (𝓡 n) q).symm x := hBg q hpoint
    have hpull := Fint.pullbackToPartialChart_inner (c q).symm (U q) (hU q) t x v w
    change (Fint.metric t).inner (e q x)
      (mfderiv (𝓡 n) (𝓡 n) (e q) x v)
      (mfderiv (𝓡 n) (𝓡 n) (e q) x w) =
        (Fint.metric t).pullbackCoefficients (c q).symm x v w at hpull
    rw [hcmap q, hFint t] at hpull
    exact (hFchart q t (Ioo_subset_Icc_self ht) x v w).trans
      ((congrArg (fun A => A v w) hvalue).trans hpull.symm)
  let : Nonempty G.limitCarrier.carrier := ⟨G.limitFlow.base⟩
  obtain ⟨F, hF, _⟩ := exists_finite_extension_of_covering_chart_flows
    htime Fint Fchart e he hcover hinterior
  have hmetric_ext (g₁ g₂ : RiemannianMetric n G.limitCarrier.carrier)
      (hinner : g₁.inner = g₂.inner) : g₁ = g₂ := by
    cases g₁
    cases g₂
    cases hinner
    rfl
  have hpast (t : ℝ) (ht : t ∈ Ico (-τ) 0) : F.metric t = Fpast.metric t := by
    apply hmetric_ext
    funext y
    ext v w
    have heq : EqOn (fun s => (F.metric s).inner y v w)
        (fun s => (Fpast.metric s).inner y v w) (Ioo (-τ) 0) := by
      intro s hs
      dsimp only
      rw [hF s hs]
      rfl
    have hleft : ContinuousOn (fun s => (F.metric s).inner y v w) (Ico (-τ) 0) := by
      intro s hs
      exact ((F.equation s ⟨hs.1, hs.2.le⟩ y v w).continuousWithinAt).mono
        (fun u hu => ⟨hu.1, hu.2.le⟩)
    have hright : ContinuousOn (fun s => (Fpast.metric s).inner y v w) (Ico (-τ) 0) :=
      fun s hs => (Fpast.equation s hs y v w).continuousWithinAt
    exact heq.of_subset_closure hleft hright
      (fun s hs => ⟨hs.1.le, hs.2⟩)
      (by rw [hclosure]; exact fun s hs => ⟨hs.1, hs.2.le⟩) ht
  refine ⟨F, fun t ht => (hpast t ht).trans (hFpast t), ?_⟩
  intro q m K hK hKdomain
  let D := Icc (-τ) 0 ×ˢ (extChartAt (𝓡 n) q).target
  let A := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
    (F.metric z.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm z.2
  change TendstoUniformlyOn
    (fun k => iteratedFDerivWithin ℝ m (f q k) D)
    (iteratedFDerivWithin ℝ m A D) atTop K
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  apply TendstoLocallyUniformlyOn.mono (s := D) _ hKdomain
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro z hz
  obtain ⟨r, hr, hball, α, hα, hellip, hbounds⟩ := hlocal q z.2 hz.2
  obtain ⟨B, _, hB, hBg, _, _, _, hjets⟩ :=
    exists_closed_flow_on_retained_chart hFlow hτ hτT G Fsrc hmetric
      q z.2 hr hball α hα hellip hbounds
  let Ω := Icc (-τ) 0 ×ˢ Metric.closedBall z.2 r
  let Γ := Icc (-τ) 0 ×ˢ Metric.ball z.2 r
  let O := (univ : Set ℝ) ×ˢ Metric.ball z.2 r
  have hΓΩ : Γ ⊆ Ω := fun p hp => ⟨hp.1, Metric.ball_subset_closedBall hp.2⟩
  have hΓD : Γ ⊆ D := fun p hp =>
    ⟨hp.1, hball (Metric.ball_subset_closedBall hp.2)⟩
  have hΓΩO : Γ = Ω ∩ O := by
    ext p
    constructor
    · intro hp
      exact ⟨hΓΩ hp, ⟨mem_univ _, hp.2⟩⟩
    · intro hp
      exact ⟨hp.1.1, hp.2.2⟩
  have hΓDO : Γ = D ∩ O := by
    ext p
    constructor
    · intro hp
      exact ⟨hΓD hp, ⟨mem_univ _, hp.2⟩⟩
    · intro hp
      exact ⟨hp.1.1, hp.2.2⟩
  have hO : IsOpen O := isOpen_univ.prod Metric.isOpen_ball
  have hΓnhds : Γ ∈ 𝓝[D] z := by
    rw [hΓDO]
    exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
      (hO.mem_nhds ⟨mem_univ _, Metric.mem_ball_self hr⟩))
  have hBA : EqOn B A Γ := by
    intro p hp
    ext v w
    have hBtime : ContinuousOn (fun s => B (s, p.2)) (Icc (-τ) 0) :=
      hB.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun s hs => ⟨hs, Metric.ball_subset_closedBall hp.2⟩)
    have hBscalar : ContinuousOn (fun s => B (s, p.2) v w) (Icc (-τ) 0) :=
      (hBtime.clm_apply continuousOn_const).clm_apply continuousOn_const
    have hAscalar : ContinuousOn (fun s => A (s, p.2) v w) (Icc (-τ) 0) := by
      intro s hs
      exact (F.equation s hs ((extChartAt (𝓡 n) q).symm p.2)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm p.2 v)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm p.2 w)).continuousWithinAt
    have heq : EqOn (fun s => B (s, p.2) v w)
        (fun s => A (s, p.2) v w) (Ioo (-τ) 0) := by
      intro s hs
      have hpoint : (s, p.2) ∈
          interior (Icc (-τ) 0 ×ˢ Metric.closedBall z.2 r) := by
        rw [interior_prod_eq, interior_Icc, interior_closedBall _ hr.ne']
        exact ⟨hs, hp.2⟩
      have hvalue : B (s, p.2) =
          (G.limitFlow.flow.metric (s + T / 2)).pullbackCoefficients
            (extChartAt (𝓡 n) q).symm p.2 := hBg hpoint
      dsimp only [A]
      rw [hF s hs, hFint s]
      exact congrArg (fun C => C v w) hvalue
    exact heq.of_subset_closure hBscalar hAscalar Ioo_subset_Icc_self
      (by rw [hclosure]) hp.1
  have hjetΩ (C : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (p : ℝ × EuclideanSpace ℝ (Fin n)) (hp : p ∈ Γ) :
      iteratedFDerivWithin ℝ m C Γ p = iteratedFDerivWithin ℝ m C Ω p := by
    rw [hΓΩO]
    exact iteratedFDerivWithin_inter_open hO ⟨mem_univ _, hp.2⟩
  have hjetD (C : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (p : ℝ × EuclideanSpace ℝ (Fin n)) (hp : p ∈ Γ) :
      iteratedFDerivWithin ℝ m C Γ p = iteratedFDerivWithin ℝ m C D p := by
    rw [hΓDO]
    exact iteratedFDerivWithin_inter_open hO ⟨mem_univ _, hp.2⟩
  have hsource (k : ℕ) : EqOn
      (iteratedFDerivWithin ℝ m (f q k) Ω)
      (iteratedFDerivWithin ℝ m (f q k) D) Γ := by
    intro p hp
    exact (hjetΩ (f q k) p hp).symm.trans (hjetD (f q k) p hp)
  have htarget : EqOn (iteratedFDerivWithin ℝ m B Ω)
      (iteratedFDerivWithin ℝ m A D) Γ := by
    intro p hp
    exact (hjetΩ B p hp).symm.trans
      (((hBA.iteratedFDerivWithin m) hp).trans (hjetD A p hp))
  exact ⟨Γ, hΓnhds, (((hjets m).mono hΓΩ).congr
    (Eventually.of_forall hsource)).congr_right htarget⟩

end PoincareConjecture.M30

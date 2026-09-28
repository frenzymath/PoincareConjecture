import PoincareConjecture.Proofs.M28.Sec10_3_Tube.LimitData
import PoincareConjecture.Proofs.M28.Mathlib.CanonicalDomainInclusion
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M28

set_option maxHeartbeats 1600000 in

theorem exists_localNonnegativeBackwardModel_of_chart_flow
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (q : M)
    (V : Set (EuclideanSpace ℝ (Fin 3))) (hV : IsOpen V) [Nonempty V]
    (hcenter : extChartAt (𝓡 3) q q ∈ V)
    (htarget : V ⊆ (extChartAt (𝓡 3) q).target)
    (tau : ℝ) (htau : 0 < tau) :
    letI := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ (F : RicciFlow 3 V (Icc (-tau) 0)),
      (∀ (x : V) v w, (F.metric 0).inner x v w =
        g.pullbackCoefficients (extChartAt (𝓡 3) q).symm x v w) →
      (∀ t ∈ Icc (-tau) 0, ∀ x : V, (F.connection t).NonnegativeCurvatureOperator x) →
      ∀ {U : Set M}, IsOpen U → q ∈ U → Nonempty (LocalNonnegativeBackwardModel g U q) := by
  let := hV.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hV.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro F hmetric hnonnegative U hU hq
  let c := extChartAt (𝓡 3) q
  have hcq : c.symm (c q) = q := extChartAt_to_inv q
  have hc : ContinuousAt c.symm (c q) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target q))).continuousAt
  have hpre : c.symm ⁻¹' U ∈ 𝓝 (c q) :=
    hc.preimage_mem_nhds (hcq.symm ▸ hU.mem_nhds hq)
  obtain ⟨rho, hrho, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hV.mem_nhds hcenter) hpre)
  let W := ball (c q) rho
  have hW : IsOpen W := isOpen_ball
  have hWV : W ⊆ V := fun _ hx => (hball hx).1
  have hWU : ∀ x ∈ W, c.symm x ∈ U := fun _ hx => (hball hx).2
  have hw : c q ∈ W := mem_ball_self hrho
  let : Nonempty W := ⟨⟨c q, hw⟩⟩
  let : ConnectedSpace W := Subtype.connectedSpace
    ((convex_ball (c q) rho).isConnected ⟨c q, hw⟩)
  let := hW.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hW.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  let j : W → V := fun x => ⟨x.val, hWV x.property⟩
  have hj : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ j :=
    Poincare.isLocalDiffeomorph_canonicalDomainInclusion hW hV hWV
  let F' := F.pullbackToCanonicalDomain W hW j hj
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) M ∞ := {
    toPartialEquiv := c.symm
    open_source := isOpen_extChartAt_target q
    open_target := isOpen_extChartAt_source q
    contMDiffOn_toFun := contMDiffOn_extChartAt_symm q
    contMDiffOn_invFun := by
      change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (extChartAt (𝓡 3) q)
        (extChartAt (𝓡 3) q).source
      simpa only [extChartAt_source] using
        (contMDiffOn_extChartAt (I := 𝓡 3) (n := ∞) (x := q)) }
  let e : W → M := fun x => c.symm x.val
  have he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e := by
    intro x
    exact (Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) W hW ∞ x).comp (𝓡 3) M
      (d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (htarget (hWV x.property)))
  have hinj : Function.Injective e := by
    intro x y hxy
    apply Subtype.ext
    exact c.symm.injOn (htarget (hWV x.property)) (htarget (hWV y.property)) hxy
  let : MeasurableSpace W := borel W
  let : BorelSpace W := ⟨rfl⟩
  let C : FlowCarrier.{0} 3 := {
    carrier := W
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := inferInstance
    chartedSpace := hW.isOpenEmbedding_subtypeVal.singletonChartedSpace
    isManifold := inferInstance
    t2Space := inferInstance
    t3Space := inferInstance
    secondCountable := inferInstance
    connected := isConnected_univ }
  refine ⟨{
    carrier := C
    duration := tau
    duration_pos := htau
    flow := F'
    embedding := e
    embedding_open := he.isLocalHomeomorph.isOpenEmbedding_of_injective hinj
    embedding_smooth := he
    image_subset := ?_
    captures := ?_
    metric_at_zero := ?_
    nonnegative := ?_ }⟩
  · rintro _ ⟨x, rfl⟩
    exact hWU x.val x.property
  · exact ⟨⟨c q, hw⟩, hcq⟩
  · intro x v w
    have hdj := Poincare.mfderiv_canonicalDomainInclusion (𝕜 := ℝ) hW hV hWV x
    have hdval : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → EuclideanSpace ℝ (Fin 3)) x =
        ContinuousLinearMap.id ℝ _ := mfderiv_extChartAt_self
    have hde (z : EuclideanSpace ℝ (Fin 3)) :
        mfderiv (𝓡 3) (𝓡 3) e x z = mfderiv (𝓡 3) (𝓡 3) c.symm x.val z := by
      have hd := mfderiv_comp_apply x
        ((d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (htarget (hWV x.property))).mdifferentiableAt
          (by simp))
        ((Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) W hW ∞ x).mdifferentiableAt
          (by simp)) z
      change mfderiv (𝓡 3) (𝓡 3) e x z = mfderiv (𝓡 3) (𝓡 3) c.symm x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : W → EuclideanSpace ℝ (Fin 3)) x z) at hd
      rw [hdval] at hd
      exact hd
    change g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) =
      (F.metric 0).inner (j x) (mfderiv (𝓡 3) (𝓡 3) j x v) (mfderiv (𝓡 3) (𝓡 3) j x w)
    rw [hdj]
    change g.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) =
      (F.metric 0).inner (j x) v w
    rw [hmetric, hde, hde]
    rfl
  · intro t ht x
    exact ((F'.connection t).nonnegativeCurvatureOperator_iff_of_local_isometry
      (F.connection t) isOpen_univ hj.contMDiff.contMDiffOn
      (fun _ _ _ _ => rfl) (mem_univ x)).2 (hnonnegative t ht (j x))

end PoincareConjecture.M28

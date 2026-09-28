import PoincareConjecture.Proofs.M35.CapGeometry.ActualFarTipRadialCurvature
import PoincareConjecture.Proofs.M35.CapGeometry.CylinderRadialPlane
import PoincareConjecture.Proofs.M35.CapGeometry.NullSectionalPlane









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

open Uniqueness

local notation "V" => EuclideanSpace ℝ (Fin 3)

@[instance_reducible] private noncomputable def nullPlaneCovectorNormedGroup :
    NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
attribute [local instance] nullPlaneCovectorNormedGroup

@[instance_reducible] private noncomputable def nullPlaneBilinearNormedGroup :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
attribute [local instance] nullPlaneBilinearNormedGroup




theorem blowupSequence_far_tip_exists_null_plane
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (hd : Tendsto (fun k => ((E.flow.metric (t k)).edist 0 (x k)).toReal *
      Real.sqrt ((E.flow.connection (t k)).scalarCurvature (x k))) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∃ u v : TangentSpace (𝓡 3) L.limit.base,
      (L.limit.flow.metric 0).inner L.limit.base u u = 1 ∧
      (L.limit.flow.metric 0).inner L.limit.base v v = 1 ∧
      (L.limit.flow.metric 0).inner L.limit.base u v = 0 ∧
      (L.limit.flow.connection 0).curvatureTensor L.limit.base u v u v = 0 := by
  classical
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  let q := L.limit.base
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
  let p := c q
  have hp : p ∈ c.target := mem_extChartAt_target (show L.limit.carrier.carrier from q)
  have hcp : c.symm p = q :=
    c.left_inv (mem_extChartAt_source (show L.limit.carrier.carrier from q))
  have hKU : ({p} : Set V) ⊆ {z | z ∈ c.target ∧ c.symm z ∈ L.exhaustion.space 0} := by
    rintro z rfl
    refine ⟨hp, ?_⟩
    rw [hcp]
    exact L.exhaustion.base_mem 0
  have hc (z : V) (hz : z ∈ c.target) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (n := ∞)
      (show L.limit.carrier.carrier from q)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3)
          (show L.limit.carrier.carrier from q)).mem_nhds hz)
  have hci (z : V) (hz : z ∈ c.target) :
      (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm
        (I := 𝓡 3) (x := (show L.limit.carrier.carrier from q)) hz
  obtain ⟨g, D, hcoeff, _hnorm⟩ := exists_local_curvature_derivative_realization
    (L.limit.flow.metric 0) (L.limit.flow.connection 0) c.symm
    (isOpen_extChartAt_target (show L.limit.carrier.carrier from q)) hp hc hci
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let hQ k := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let G k := M13.scaleSmoothMetric (E.flow.metric (t (L.subsequence k))) (Q k) (hQ k)
  let B (k : ℕ) (a b : Fin 3) (z : V) :=
    fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence k)) (Q k)
      (fun w => ((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ w).val) q a b (0, z)
  let H (a b : Fin 3) (z : V) :=
    (L.limit.flow.metric 0).pullbackCoefficients c.symm z
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
  have hxne : ∀ᶠ k in atTop, x (L.subsequence k) ≠ 0 := by
    filter_upwards [(hd.comp L.subsequence_strictMono.tendsto_atTop).eventually
      (eventually_gt_atTop 0)] with k hk
    intro heq
    have hzero : (E.flow.metric (t (L.subsequence k))).edist 0 (x (L.subsequence k)) = 0 := by
      rw [heq]
      exact @edist_self StandardCapSpace
        (E.flow.metric (t (L.subsequence k))).toEMetricSpace.toPseudoEMetricSpace 0
    have hfalse := hk
    simp only [Function.comp_apply, hzero, ENNReal.toReal_zero, zero_mul,
      lt_self_iff_false] at hfalse
  have hreal : ∀ᶠ k : ℕ in atTop,
      ∃ gd : Σ g' : RiemannianMetric 3 V, LeviCivitaData g' × V × V,
        (∀ᶠ z in 𝓝 p, ∀ a b : Fin 3,
          gd.1.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) = B k a b z) ∧
        gd.1.inner p gd.2.2.1 gd.2.2.1 = 1 ∧ gd.1.inner p gd.2.2.2 gd.2.2.2 = 1 ∧
        gd.1.inner p gd.2.2.1 gd.2.2.2 = 0 ∧
        gd.2.1.curvatureTensor p gd.2.2.1 gd.2.2.2 gd.2.2.1 gd.2.2.2 =
          radialMixedCurvatureFactor (G k) ‖x (L.subsequence k)‖ /
            axisRadialCoefficient (G k) ‖x (L.subsequence k)‖ := by
    filter_upwards [hxne] with k hk
    have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
    have hpU : c.symm p ∈ L.exhaustion.space k := by
      rw [hcp]
      exact L.exhaustion.base_mem k
    have hbase : ((L.embedding k).forward 0 hzero (c.symm p)).val = x (L.subsequence k) := by
      rw [hcp]
      exact congrArg (fun z : (generalizedFlow E.flow.base.flow).point => z.2.val)
        (L.base_preserving k _)
    obtain ⟨gk, Dk, uk, vk, hco, hunitu, hunitv, horth, hvalue⟩ :=
      exists_cylinder_radial_plane_realization E.flow.base.flow (L.embedding k)
        (L.exhaustion.space_open k) hzero ((L.embedding k).forward 0 hzero q).property
        (E.rotation_invariant (t (L.subsequence k)) (ht (L.subsequence k))) q hp hpU
        (by change ((L.embedding k).forward 0 hzero (c.symm p)).val ≠ 0; rwa [hbase])
    refine ⟨⟨gk, Dk, uk, vk⟩, hco, hunitu, hunitv, horth, ?_⟩
    change Dk.curvatureTensor p uk vk uk vk =
      radialMixedCurvatureFactor (G k) ‖((L.embedding k).forward 0 hzero (c.symm p)).val‖ /
        axisRadialCoefficient (G k) ‖((L.embedding k).forward 0 hzero (c.symm p)).val‖ at hvalue
    rwa [hbase] at hvalue
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hlimcoeff (a b : Fin 3) :
      (fun z => g.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p] H a b := by
    filter_upwards [hcoeff] with z hz
    exact congrArg (fun A : V →L[ℝ] V →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) hz
  have hjets (r : ℕ) : Tendsto
      (fun k => iteratedFDeriv ℝ r (gd k).1.euclideanCoefficients p) atTop
        (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients p)) := by
    apply metric_jet_tendsto_of_scalar_jets
    intro a b
    rw [(hlimcoeff a b).iteratedFDeriv ℝ r |>.self_of_nhds]
    have herr : Tendsto (fun k => iteratedFDeriv ℝ r (B k a b) p -
        iteratedFDeriv ℝ r (H a b) p) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro eta heta
      obtain ⟨N, _, hN⟩ := blowupSequence_terminal_spatial_CInfinity P E t x ht hR L q
        0 r {p} isCompact_singleton hKU eta heta
      filter_upwards [eventually_ge_atTop N] with k hk
      have hnk := hN k hk a b p (mem_singleton _)
      change ‖iteratedFDeriv ℝ r (B k a b) p - iteratedFDeriv ℝ r (H a b) p‖ < eta at hnk
      simpa only [dist_zero_right] using hnk
    have hjet : Tendsto (fun k => iteratedFDeriv ℝ r (B k a b) p) atTop
        (𝓝 (iteratedFDeriv ℝ r (H a b) p)) := by
      simpa only [sub_add_cancel, zero_add] using herr.add_const (iteratedFDeriv ℝ r (H a b) p)
    apply hjet.congr'
    filter_upwards [hgd] with k hk
    have heq : (fun z => (gd k).1.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p] B k a b :=
      hk.1.mono (fun z hz => hz a b)
    exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).symm
  have hcurv : Tendsto (fun k => (gd k).2.1.curvatureTensor p
      (gd k).2.2.1 (gd k).2.2.2 (gd k).2.2.1 (gd k).2.2.2) atTop (𝓝 0) := by
    apply (blowupSequence_far_tip_radial_sectional_tendsto_zero P E t x ht hR hd L).congr'
    exact hgd.mono (fun _ hk => hk.2.2.2.2.symm)
  obtain ⟨u, v, hu, hv, huv, hzero⟩ := exists_null_sectional_plane_of_metric_jets
    (fun k => (gd k).2.1) D (fun _ => p) p (fun r _ => hjets r)
    (fun k => (gd k).2.2.1) (fun k => (gd k).2.2.2)
    (hgd.mono (fun _ hk => ⟨hk.2.1, hk.2.2.1, hk.2.2.2.1⟩)) hcurv
  have hm : ∀ᶠ z in 𝓝 p, ∀ a b : V, g.inner z a b =
      (L.limit.flow.metric 0).inner (c.symm z)
        (mfderiv (𝓡 3) (𝓡 3) c.symm z a) (mfderiv (𝓡 3) (𝓡 3) c.symm z b) := by
    filter_upwards [hcoeff] with z hz a b
    exact congrArg (fun B : V →L[ℝ] V →L[ℝ] ℝ => B a b) hz
  have hi : ∀ᶠ z in 𝓝 p, (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible :=
    Filter.mem_of_superset
      ((isOpen_extChartAt_target (show L.limit.carrier.carrier from q)).mem_nhds hp) hci
  refine ⟨mfderiv (𝓡 3) (𝓡 3) c.symm p u, mfderiv (𝓡 3) (𝓡 3) c.symm p v, ?_, ?_, ?_, ?_⟩
  · have h := (hm.self_of_nhds u u).symm.trans hu
    rwa [hcp] at h
  · have h := (hm.self_of_nhds v v).symm.trans hv
    rwa [hcp] at h
  · have h := (hm.self_of_nhds u v).symm.trans huv
    rwa [hcp] at h
  · have h := (D.curvatureTensor_eq_pullback_euclidean
      (L.limit.flow.connection 0) (hc p hp) hi hm u v u v).symm.trans hzero
    rwa [hcp] at h

end PoincareConjecture.M35.OrdinaryRealization

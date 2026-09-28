import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Continuation.Gluing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Gluing.MetricJets

set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

namespace Surgery.RegularHistory.Gluing

variable {S : GeneralizedSliceCarrier.{u}}

theorem singularMetricCoefficient_eq_localFrame
    (g : RiemannianMetric 3 S.carrier) (x0 : S.carrier) (a b : Fin 3)
    {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) x0).target) :
    let V := EuclideanSpace ℝ (Fin 3)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 3)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    singularMetricCoefficient g x0 a b z =
      g.inner (c.symm z) (E a (c.symm z)) (E b (c.symm z)) := by
  let V := EuclideanSpace ℝ (Fin 3)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 3)) x0
  let cb := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let E := e.localFrame cb
  let y := c.symm z
  have hy : y ∈ e.baseSet := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using c.map_target hz
  have he : e.symmL ℝ y = mfderiv (𝓡 3) (𝓡 3) c.symm z := by
    have hh := TangentBundle.symmL_trivializationAt (I := 𝓡 3) (x₀ := x0)
      (c.map_target hz)
    simp only [extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, Set.range_id,
      mfderivWithin_univ] at hh
    change e.symmL ℝ y = mfderiv (𝓡 3) (𝓡 3) c.symm (c y) at hh
    rwa [c.right_inv hz] at hh
  have hframe (i : Fin 3) :
      E i y = e.symmL ℝ y (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
    calc
      E i y = e.basisAt cb hy i := e.localFrame_apply_of_mem_baseSet cb hy
      _ = e.symm y (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
        simp only [Trivialization.basisAt, Module.Basis.map_apply, cb,
          OrthonormalBasis.coe_toBasis, Trivialization.linearEquivAt_symm_apply]
      _ = e.symmL ℝ y (EuclideanSpace.basisFun (Fin 3) ℝ i) :=
        (e.symmL_apply hy _).symm
  change g.inner y
      (mfderiv (𝓡 3) (𝓡 3) c.symm z
        (EuclideanSpace.basisFun (Fin 3) ℝ a))
      (mfderiv (𝓡 3) (𝓡 3) c.symm z
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) = g.inner y (E a y) (E b y)
  rw [hframe a, hframe b, he]
  rfl

theorem singularMetricCoefficient_jets_eq_localFrame
    (g : RiemannianMetric 3 S.carrier) (x0 : S.carrier) (k : ℕ) (a b : Fin 3)
    {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) x0).target) :
    let V := EuclideanSpace ℝ (Fin 3)
    let c := chartAt V x0
    let e := trivializationAt V (TangentSpace (𝓡 3)) x0
    let E := e.localFrame (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    iteratedFDeriv ℝ k (singularMetricCoefficient g x0 a b) z =
      iteratedFDeriv ℝ k
        (fun w => g.inner (c.symm w) (E a (c.symm w)) (E b (c.symm w))) z := by
  let V := EuclideanSpace ℝ (Fin 3)
  let c := chartAt V x0
  let e := trivializationAt V (TangentSpace (𝓡 3)) x0
  let E := e.localFrame (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hnear : singularMetricCoefficient g x0 a b =ᶠ[𝓝 z]
      (fun w => g.inner (c.symm w) (E a (c.symm w)) (E b (c.symm w))) := by
    filter_upwards [c.open_target.mem_nhds hz] with w hw
    exact singularMetricCoefficient_eq_localFrame g x0 a b hw
  exact (hnear.iteratedFDeriv ℝ k).self_of_nhds

end Surgery.RegularHistory.Gluing

theorem SurgeryMetricLimitOn.exists_zero_start_gluing
    {S : GeneralizedSliceCarrier.{u}} {T δ : ℝ}
    {F : RicciFlow 3 S.carrier (Ico 0 T)}
    {G : RicciFlow 3 S.carrier (Ico T (T + δ))}
    (h : SurgeryMetricLimitOn S S F.metric (G.metric T) id univ T)
    (hT : 0 < T) (hδ : 0 < δ) :
    ∃ H : RicciFlow 3 S.carrier (Ico 0 (T + δ)),
      EqOn F.metric H.metric (Ico 0 T) ∧ EqOn G.metric H.metric (Ico T (T + δ)) := by
  apply RicciFlow.Local.exists_ricciFlow_gluing_of_uniform_metric_jets hT hδ F G
  intro x0
  dsimp only
  intro k K hK hKt a b
  have hKe : K ⊆ (extChartAt (𝓡 3) x0).target := by
    simpa only [extChartAt_target, modelWithCornersSelf_coe_symm,
      modelWithCornersSelf_coe, preimage_id, range_id, inter_univ] using hKt
  have hlim := h.tendstoUniformlyOn x0 (mem_univ _) K hK hKe (subset_univ _) k a b
  change TendstoUniformlyOn
    (fun t => iteratedFDeriv ℝ k (singularMetricCoefficient (F.metric t) x0 a b))
    (iteratedFDeriv ℝ k (singularMetricCoefficient (G.metric T) x0 a b)) (𝓝[<] T) K at hlim
  exact (hlim.congr (Eventually.of_forall (fun t z hz =>
    Surgery.RegularHistory.Gluing.singularMetricCoefficient_jets_eq_localFrame
      (F.metric t) x0 k a b (hKt hz)))).congr_right (fun z hz =>
    Surgery.RegularHistory.Gluing.singularMetricCoefficient_jets_eq_localFrame
      (G.metric T) x0 k a b (hKt hz))

end PoincareConjecture

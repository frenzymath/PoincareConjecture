import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.ChangingParametrization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.CylinderCoefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Transitions








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set Filter
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Calculus

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem smooth_zero_convergence_changing_cylinder_parametrizations
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    let U : Set RoundCylinderCoordinates :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ
    let F : ℕ → RoundCylinderCoordinates → G.limitCarrier.carrier :=
      fun i x => Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
    let A := fun i x =>
      ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
        (fun y => ((G.embedding i).toFun (0, F i y)).2) x -
      (G.limitFlow.metricAt t).parametrizedCoefficients (F i) x
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (A i)) (fun _ => 0) atTop K := by
  let U : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 3 ×ˢ univ
  let V : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_univ
  have hV : IsOpen V := Metric.isOpen_ball.prod isOpen_univ
  let f := fun x : RoundCylinderCoordinates =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm x.1, x.2)
  let F := fun i (x : RoundCylinderCoordinates) =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
  let c := fun i => roundCylinderCoordinateTransition p (q i)
  let A := fun i x =>
    ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
      (fun y => ((G.embedding i).toFun (0, F i y)).2) x -
    (G.limitFlow.metricAt t).parametrizedCoefficients (F i) x
  let D := fun i x =>
    ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
      (fun y => ((G.embedding i).toFun (0, f (c i y))).2) x -
    (G.limitFlow.metricAt t).parametrizedCoefficients (f ∘ c i) x
  let e : RoundCylinderCoordinates ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨hDlocal, hDjet⟩ := G.smooth_zero_convergence_changing_parametrized_coefficients
    hzero e hU hV (hΦ.comp (cylinderChart_symm_smooth p)).contMDiffOn
    (fun x hx => ⟨V, hV, hx, Eventually.of_forall fun i =>
      contDiffOn_roundCylinderCoordinateTransition p (q i) (hpq i)⟩)
    (fun K hK hKV m => by
      obtain ⟨C, _, hC⟩ := exists_uniform_roundCylinderCoordinateTransition_jet_bound
        p q hpq hK hKV m
      exact ⟨C, Eventually.of_forall hC⟩)
    (fun K hK hKV => by
      obtain ⟨T, hT, hTU, hmap⟩ := exists_compact_roundCylinderCoordinateTransition_target
        p q hpq hK hKV
      exact ⟨T, hT, hTU, Eventually.of_forall hmap⟩) ht
  have heq (i : ℕ) : EqOn (D i) (A i) V := by
    intro x hx
    have hpair := roundCylinderCoordinateTransition_chart_inverse_eventuallyEq p (q i) (hpq i) hx
    have hf : (f ∘ c i) =ᶠ[𝓝 x] F i := hpair.fun_comp Φ
    have hsource : (fun y => ((G.embedding i).toFun (0, f (c i y))).2) =ᶠ[𝓝 x]
        (fun y => ((G.embedding i).toFun (0, F i y)).2) :=
      hf.fun_comp (fun z => ((G.embedding i).toFun (0, z)).2)
    exact congrArg₂ (fun v w => v - w)
      (((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients_congr_of_eventuallyEq hsource)
      ((G.limitFlow.metricAt t).parametrizedCoefficients_congr_of_eventuallyEq hf)
  change (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, hs⟩ := hDlocal x hx
    refine ⟨V ∩ W, hV.inter hW, ⟨hx, hxW⟩, ?_⟩
    exact hs.mono fun i hi => (hi.mono inter_subset_right).congr
      (fun y hy => (heq i hy.1).symm)
  · intro m K hK hKV
    exact (hDjet m K hK hKV).congr (Eventually.of_forall fun i x hx =>
      (eqOn_iteratedFDeriv_of_isOpen hV (heq i) m) (hKV hx))

theorem smooth_zero_convergence_changing_cylinder_coefficients
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    {t : ℝ} (ht : t ∈ Ioo a b) (v w : Fin 3) :
    let U : Set RoundCylinderCoordinates :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ
    let B := fun i => roundCylinderPullback ((S.flow (G.subsequence i)).metricAt t)
      (fun z => ((G.embedding i).toFun (0, Φ z)).2)
    let B₀ := roundCylinderPullback (G.limitFlow.metricAt t) Φ
    let A := fun i x =>
      roundCylinderTensorCoefficient (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
      roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (A i)) (fun _ => 0) atTop K := by
  let U : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_univ
  let f := fun i (z : RoundCylinderSpace) => ((G.embedding i).toFun (0, Φ z)).2
  let F := fun i (x : RoundCylinderCoordinates) =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
  let E := fun i x =>
    ((S.flow (G.subsequence i)).metricAt t).parametrizedCoefficients
      (fun y => ((G.embedding i).toFun (0, F i y)).2) x -
    (G.limitFlow.metricAt t).parametrizedCoefficients (F i) x
  let B := fun i => roundCylinderPullback ((S.flow (G.subsequence i)).metricAt t) (f i)
  let B₀ := roundCylinderPullback (G.limitFlow.metricAt t) Φ
  let A := fun i x =>
    roundCylinderTensorCoefficient (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
    roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
  let L := (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis w)).comp
    (ContinuousLinearMap.apply ℝ (RoundCylinderCoordinates →L[ℝ] ℝ)
      (roundCylinderCoordinateBasis v))
  obtain ⟨hElocal, hEjet⟩ := G.smooth_zero_convergence_changing_cylinder_parametrizations
    hzero hΦ p q hpq ht
  obtain ⟨hDlocal, hDjet⟩ := smooth_convergence_continuousLinearMap_comp L hU
    (contDiffOn_const (c := (0 : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ)))
    hElocal (fun m K hK hKU =>
      (hEjet m K hK hKU).congr_right (fun _ _ => by simp))
  have hnear (K : Set RoundCylinderCoordinates) (hK : IsCompact K) (hKU : K ⊆ U) :
      ∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ᶠ i in atTop, EqOn (L ∘ E i) (A i) W := by
    obtain ⟨D, hD, hKD, _⟩ := exists_compact_between hK hU hKU
    have hcompact : IsCompact (univ ×ˢ (Prod.snd '' D) : Set RoundCylinderSpace) :=
      isCompact_univ.prod (hD.image continuous_snd)
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hcompact.image hΦ.continuous)
    refine ⟨interior D, isOpen_interior, hKD, ?_⟩
    filter_upwards [eventually_ge_atTop j] with i hji x hx
    have hmem : F i x ∈ G.exhaustion i := G.exhaustion_monotone hji
      (hj (mem_image_of_mem Φ ⟨mem_univ _, mem_image_of_mem Prod.snd (interior_subset hx)⟩))
    have hfs : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (f i)
        ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2) :=
      (((G.embedding i).spatialMap_contMDiffAt (G.exhaustion_open i) hzero hmem).comp
        ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
        (hΦ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2))).mdifferentiableAt (by simp)
    have hs := roundCylinderTensorCoefficient_pullback_eq
      ((S.flow (G.subsequence i)).metricAt t) (q i) (f i) x hfs v w
    have hlim := roundCylinderTensorCoefficient_pullback_eq
      (G.limitFlow.metricAt t) (q i) Φ x ((hΦ _).mdifferentiableAt (by simp)) v w
    exact (congrArg₂ (fun x y => x - y) hs hlim).symm
  change (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨V, hV, hxV, hs⟩ := hDlocal x hx
    obtain ⟨W, hW, hxW, heq⟩ := hnear {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW (mem_singleton x)⟩, ?_⟩
    filter_upwards [hs, heq] with i hi hEq
    exact (hi.mono inter_subset_left).congr (fun y hy => (hEq hy.2).symm)
  · intro m K hK hKU
    obtain ⟨W, hW, hKW, heq⟩ := hnear K hK hKU
    apply ((hDjet m K hK hKU).congr ?_).congr_right (fun _ _ => by simp [Function.comp_def])
    filter_upwards [heq] with i hi x hx
    exact (eqOn_iteratedFDeriv_of_isOpen hW hi m) (hKW hx)

end PoincareConjecture.PointedGeometricConvergence

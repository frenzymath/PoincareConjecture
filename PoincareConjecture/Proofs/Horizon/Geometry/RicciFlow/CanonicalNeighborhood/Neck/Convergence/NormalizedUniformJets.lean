import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.UniformJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Scalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Poincare.Analysis.Calculus
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

private theorem constant_jets_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀)) (m : ℕ) (K : Set E) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fun _ : E => s k))
      (iteratedFDeriv ℝ m (fun _ : E => s₀)) atTop K := by
  cases m with
  | zero =>
    have h := ((continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous.tendsto s₀).comp hs
    exact h.tendstoUniformlyOn_const K
  | succ m =>
    simp_rw [iteratedFDeriv_succ_const]
    exact tendsto_const_nhds.tendstoUniformlyOn_const K

private theorem smooth_zero_convergence_scalar_errors
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {e : ℕ → E → ℝ} {A : E → ℝ}
    (hA : ContDiffOn ℝ ∞ A U)
    (helocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (e i) W)
    (hejet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (e i)) (fun _ => 0) atTop K)
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀)) :
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (fun y => s i * e i y + (s i - s₀) * A y) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (fun y => s i * e i y + (s i - s₀) * A y))
      (fun _ => 0) atTop K := by
  obtain ⟨hfl, hfj⟩ := smooth_convergence_bilinear_on_finiteDimensional hU
    (ContinuousLinearMap.mul ℝ ℝ) (contDiffOn_const (c := s₀))
    (contDiffOn_const (c := (0 : ℝ)))
    (fun x _ => ⟨univ, isOpen_univ, mem_univ x,
      Eventually.of_forall fun _ => contDiffOn_const⟩)
    helocal (fun m K _ _ => constant_jets_tendsto hs m K)
    (fun m K hK hKU => (hejet m K hK hKU).congr_right (fun _ _ => by simp))
  have hdelta : Tendsto (fun i => s i - s₀) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hs.sub_const s₀
  obtain ⟨hgl, hgj⟩ := smooth_convergence_bilinear_on_finiteDimensional hU
    (ContinuousLinearMap.mul ℝ ℝ) (contDiffOn_const (c := (0 : ℝ))) hA
    (fun x _ => ⟨univ, isOpen_univ, mem_univ x,
      Eventually.of_forall fun _ => contDiffOn_const⟩)
    (fun x hx => ⟨U, hU, hx, Eventually.of_forall fun _ => hA⟩)
    (fun m K _ _ => constant_jets_tendsto hdelta m K)
    (fun m K _ _ => by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε)
  have hflocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (fun y => s i * e i y) W := by
    intro x hx
    obtain ⟨W, hW, hxW, _, hi⟩ := hfl x hx
    exact ⟨W, hW, hxW, hi⟩
  have hglocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (fun y => (s i - s₀) * A y) W := by
    intro x hx
    obtain ⟨W, hW, hxW, _, hi⟩ := hgl x hx
    exact ⟨W, hW, hxW, hi⟩
  constructor
  · intro x hx
    obtain ⟨V, hV, hxV, hf⟩ := hflocal x hx
    obtain ⟨W, hW, hxW, hg⟩ := hglocal x hx
    refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW⟩, ?_⟩
    filter_upwards [hf, hg] with i hif hig
    exact (hif.mono inter_subset_left).add (hig.mono inter_subset_right)
  · intro m K hK hKU
    have h := (hfj m K hK hKU).add (hgj m K hK hKU)
    apply (h.congr ?_).congr_right ?_
    · filter_upwards [eventually_contDiffAt_on_compact hK hKU hflocal,
        eventually_contDiffAt_on_compact hK hKU hglocal] with i hif hig x hx
      exact (iteratedFDeriv_add_apply
        ((hif x hx).of_le (by exact_mod_cast le_top))
        ((hig x hx).of_le (by exact_mod_cast le_top))).symm
    · intro x hx
      simp

theorem smooth_zero_convergence_normalized_changing_cylinder_coefficients
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    {t : ℝ} (ht : t ∈ Ioo a b) {s : ℕ → ℝ} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hs : Tendsto s atTop (𝓝 s₀))
    (hround : (fun z v w => s₀ * roundCylinderPullback (G.limitFlow.metricAt t) Φ z v w) =
      EvolvingRoundCylinderMetric 0)
    (v w : Fin 3) :
    let U : Set RoundCylinderCoordinates :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ
    let B : ℕ → RoundCylinderTwoTensor := fun i z v w =>
      s i * roundCylinderPullback ((S.flow (G.subsequence i)).metricAt t)
        (fun z => ((G.embedding i).toFun (0, Φ z)).2) z v w
    let E := fun i x =>
      roundCylinderTensorCoefficient (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (E i) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (E i)) (fun _ => 0) atTop K := by
  let U : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_univ
  let B := fun i => roundCylinderPullback ((S.flow (G.subsequence i)).metricAt t)
    (fun z => ((G.embedding i).toFun (0, Φ z)).2)
  let B₀ := roundCylinderPullback (G.limitFlow.metricAt t) Φ
  let e := fun i x =>
    roundCylinderTensorCoefficient (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
    roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
  let A := fun x => s₀⁻¹ * roundCylinderGram 0
    (chartAt (EuclideanSpace ℝ (Fin 2)) p) x v w
  have hA : ContDiffOn ℝ ∞ A U :=
    (contDiff_const.mul (contDiff_roundCylinderGram 0 p v w)).contDiffOn
  have hmodel (i : ℕ) (x : RoundCylinderCoordinates) :
      s₀ * roundCylinderTensorCoefficient B₀
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) p) x v w := by
    have h := congrArg (fun T => roundCylinderTensorCoefficient T
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w) hround
    change s₀ * roundCylinderTensorCoefficient B₀
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w =
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w at h
    rw [roundCylinderGram_eq_chart_center 0 p (q i)] at h
    exact h
  have hlim (i : ℕ) (x : RoundCylinderCoordinates) :
      roundCylinderTensorCoefficient B₀
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w = A x := by
    dsimp [A]
    rw [← hmodel i x, ← mul_assoc, inv_mul_cancel₀ hs₀.ne', one_mul]
  obtain ⟨helocal, hejet⟩ := G.smooth_zero_convergence_changing_cylinder_coefficients
    hzero hΦ p q hpq ht v w
  have h := smooth_zero_convergence_scalar_errors hU hA helocal hejet hs
  have heq (i : ℕ) :
      (fun x => s i * e i x + (s i - s₀) * A x) =
      (fun x => roundCylinderTensorCoefficient (fun z v w => s i * B i z v w)
        (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
        roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w) := by
    funext x
    change s i * (roundCylinderTensorCoefficient (B i)
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
      roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w) +
      (s i - s₀) * A x = s i * roundCylinderTensorCoefficient (B i)
      (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
      roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
    rw [roundCylinderGram_eq_chart_center 0 p (q i), ← hmodel i x, hlim i x]
    ring
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, hi⟩ := h.1 x hx
    refine ⟨W, hW, hxW, hi.mono fun i hsi => ?_⟩
    exact (congrArg (fun f => ContDiffOn ℝ ∞ f W) (heq i)).mp hsi
  · intro m K hK hKU
    exact (h.2 m K hK hKU).congr (Eventually.of_forall fun i x _ =>
      congrArg (fun f => iteratedFDeriv ℝ m f x) (heq i))

theorem tendstoUniformlyOn_normalized_cylinder_jet_error
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    {t : ℝ} (ht : t ∈ Ioo a b) {s : ℕ → ℝ} {s₀ : ℝ}
    (hs₀ : 0 < s₀) (hs : Tendsto s atTop (𝓝 s₀))
    (hround : (fun z v w => s₀ * roundCylinderPullback (G.limitFlow.metricAt t) Φ z v w) =
      EvolvingRoundCylinderMetric 0)
    (order : ℕ) {J : Set ℝ} (hJ : IsCompact J) :
    TendstoUniformlyOn
      (fun i => roundCylinderJetErrorSquared 0
        (fun z v w => s i * roundCylinderPullback ((S.flow (G.subsequence i)).metricAt t)
          (fun z => ((G.embedding i).toFun (0, Φ z)).2) z v w) order)
      (fun _ => 0) atTop (univ ×ˢ J) := by
  apply Poincare.Topology.tendstoUniformlyOn_prod_of_isCompact_of_locally_moving_points
    (g := fun _ : ℝ => (0 : ℝ))
    (isCompact_univ : IsCompact (univ : Set UnitTwoSphere))
  intro p _
  refine ⟨Metric.ball p (1 / 2), Metric.isOpen_ball, Metric.mem_ball_self (by norm_num), ?_⟩
  intro q hq
  have hpq (i : ℕ) : ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2 := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using (hq i).2
  have hc (v w : Fin 3) := G.smooth_zero_convergence_normalized_changing_cylinder_coefficients
    hzero hΦ p q hpq ht hs₀ hs hround v w
  dsimp only at hc
  have h := tendstoUniformlyOn_roundCylinder_changingChart_error_jetSum (by norm_num) p q
    (Metric.isOpen_ball.prod isOpen_univ)
    (fun v w => (hc v w).1) (fun v w => (hc v w).2) order
    (isCompact_singleton.prod hJ)
    (show ({0} : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ J ⊆
        Metric.ball 0 (1 / 2) ×ˢ univ from by
      rintro ⟨x, z⟩ ⟨hx, hz⟩
      have hx0 : x = 0 := mem_singleton_iff.mp hx
      subst x
      exact ⟨Metric.mem_ball_self (by norm_num), mem_univ z⟩)
  have hh := (h.comp (fun z : ℝ => (0, z))).mono
    (show J ⊆ (fun z : ℝ => ((0 : EuclideanSpace ℝ (Fin 2)), z)) ⁻¹'
        (({0} : Set (EuclideanSpace ℝ (Fin 2))) ×ˢ J) from
      fun z hz => ⟨mem_singleton 0, hz⟩)
  simpa only [roundCylinderJetErrorSquared, sphere_chart_center, Function.comp_def] using hh

private theorem scalar_neck_scale_inverse_sq {R : ℝ} (hR : 0 < R) :
    (R ^ (-1 / 2 : ℝ))⁻¹ ^ (2 : ℕ) = R := by
  rw [neg_div, Real.rpow_neg hR.le, inv_inv, ← Real.rpow_natCast,
    ← Real.rpow_mul hR.le]
  norm_num

theorem tendstoUniformlyOn_scalarNormalized_cylinder_jet_error
    {a b : ℝ} {S : PointedFlowSequence 3 a b}
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    {Φ : RoundCylinderSpace → G.limitCarrier.carrier}
    (hΦ : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ)
    (hR : 0 < (G.limitFlow.flow.connection 0).scalarCurvature G.limitFlow.base)
    (hround : (fun z v w => (G.limitFlow.flow.connection 0).scalarCurvature G.limitFlow.base *
      roundCylinderPullback (G.limitFlow.metricAt 0) Φ z v w) = EvolvingRoundCylinderMetric 0)
    (order : ℕ) {J : Set ℝ} (hJ : IsCompact J) :
    let R : ℕ → ℝ := fun i => ((S.flow (G.subsequence i)).flow.connection 0).scalarCurvature
      (S.flow (G.subsequence i)).base
    let scale : ℕ → ℝ := fun i => R i ^ (-1 / 2 : ℝ)
    (∀ᶠ i in atTop, 0 < R i ∧ 0 < scale i ∧ (scale i)⁻¹ ^ (2 : ℕ) = R i) ∧
    TendstoUniformlyOn
      (fun i => roundCylinderJetErrorSquared 0
        (fun z v w => (scale i)⁻¹ ^ (2 : ℕ) *
          roundCylinderPullback ((S.flow (G.subsequence i)).metricAt 0)
            (fun z => ((G.embedding i).toFun (0, Φ z)).2) z v w) order)
      (fun _ => 0) atTop (univ ×ˢ J) := by
  dsimp only
  have hs := G.tendsto_scalarCurvature_at_zero_base hzero
  have hpos := hs.eventually (isOpen_Ioi.mem_nhds hR)
  constructor
  · filter_upwards [hpos] with i hi
    exact ⟨hi, Real.rpow_pos_of_pos hi _, scalar_neck_scale_inverse_sq hi⟩
  · have h := G.tendstoUniformlyOn_normalized_cylinder_jet_error
      hzero hΦ hzero hR hs hround order hJ
    apply h.congr
    filter_upwards [hpos] with i hi z _
    rw [scalar_neck_scale_inverse_sq hi]

end PoincareConjecture.PointedGeometricConvergence

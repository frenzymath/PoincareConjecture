import PoincareConjecture.Proofs.M47.LimitFiniteEndpointComplete
import PoincareConjecture.Proofs.M47.TerminalCurvatureOpenInclusion
import PoincareConjecture.Proofs.M04.FlowRiemannRegularity
import PoincareConjecture.Proofs.M04.ScalarEvolution
import PoincareConjecture.Proofs.M34.Thm12_5_Existence.CompactCurvatureBound
import PoincareConjecture.Proofs.M35.Prop12_31.CurvatureOperator
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

private theorem inclusion_curvature_readouts
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (U : TopologicalSpace.Opens M)
    {h : RiemannianMetric 3 U} (D' : LeviCivitaData h)
    (hmetric : ∀ (x : U) (v w : E), h.inner x v w = g.inner x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w)) (x : U) :
    D'.scalarCurvature x = D.scalarCurvature x.val ∧
      (∀ v w z a : E, D'.curvatureTensor x v w z a = D.curvatureTensor x.val v w z a) ∧
      D'.curvatureTensorNorm x = D.curvatureTensorNorm x.val := by
  have hstraight : ∀ (y : U) (v w : E), h.inner y v w = g.inner y.val v w := by
    intro y v w
    simpa only [Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal_apply]
      using hmetric y v w
  have hread := terminalCurvature_open_inclusion_readouts D U D' hstraight x
  exact ⟨hread.1, hread.2.1, D'.curvatureTensorNorm_eq_of_local_isometry D
    isOpen_univ contMDiff_subtype_val.contMDiffOn
    (fun y _ v w => hmetric y v w) (mem_univ x)⟩

private theorem curvature_bounds_of_right_limit
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {J : Set ℝ} (A : RicciFlow 3 M J) (hJ : IsOpen J) {t0 K : ℝ} (ht0 : t0 ∈ J)
    (x : M) (htail : ∀ᶠ t in 𝓝[>] t0,
      (A.connection t).scalarCurvature x ≤ K ∧
        (A.connection t).curvatureTensorNorm x ≤ 9 * K) :
    (A.connection t0).scalarCurvature x ≤ K ∧
      (A.connection t0).curvatureTensorNorm x ≤ 9 * K := by
  have hscalar := ((A.contDiffOn_scalarCurvature_timeSlice x).continuousOn t0 ht0).continuousAt
    (hJ.mem_nhds ht0)
  have hnorm : ContinuousAt (fun t => (A.connection t).curvatureTensorNorm x) t0 := by
    have hprod : J ×ˢ (univ : Set M) ∈ 𝓝 (t0, x) :=
      (hJ.prod isOpen_univ).mem_nhds ⟨ht0, mem_univ x⟩
    have hc := ((M34.continuousOn_flow_curvatureTensorNorm A) (t0, x)
      ⟨ht0, mem_univ x⟩).continuousAt hprod
    have hp : ContinuousAt (fun t : ℝ => (t, x)) t0 :=
      continuous_id.continuousAt.prodMk continuous_const.continuousAt
    exact Filter.Tendsto.comp (f := fun t : ℝ => (t, x))
      (g := fun p : ℝ × M => (A.connection p.1).curvatureTensorNorm p.2) hc hp
  have hscalarLimit : Tendsto (fun t => (A.connection t).scalarCurvature x)
      (𝓝[>] t0) (𝓝 ((A.connection t0).scalarCurvature x)) :=
    hscalar.mono_left nhdsWithin_le_nhds
  have hnormLimit : Tendsto (fun t => (A.connection t).curvatureTensorNorm x)
      (𝓝[>] t0) (𝓝 ((A.connection t0).curvatureTensorNorm x)) :=
    hnorm.mono_left nhdsWithin_le_nhds
  exact ⟨le_of_tendsto hscalarLimit (htail.mono fun _ ht => ht.1),
    le_of_tendsto hnormLimit (htail.mono fun _ ht => ht.2)⟩

variable {S : GeneralizedBlowupSequence.{u}} {H : ℝ≥0∞}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance finiteEndpointCurvatureTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteEndpointCurvatureCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteEndpointCurvatureManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

local notation "U" => (fun m : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space m) (G.exhaustion.space_open m))

include G in
private theorem old_right_tail (hfinite : H ≠ ⊤) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ t in 𝓝[>] (-H.toReal),
      t ∈ Ioo (-H.toReal - d / 8) (-H.toReal + d / 4) ∧
        t ∈ blowupBackwardInterval H := by
  have hH : 0 < H := by simpa using G.limit.zero_mem.2
  have hT := limitFinite_horizon_pos hH hfinite
  have ht0 : -H.toReal ∈ Ioo (-H.toReal - d / 8) (-H.toReal + d / 4) :=
    ⟨by linarith, by linarith⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds ht0),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (neg_lt_zero.mpr hT)),
    self_mem_nhdsWithin] with t htJ htneg htright
  refine ⟨htJ, ?_⟩
  rw [limitFinite_domain_eq hfinite]
  exact ⟨htright, htneg.le⟩

theorem limitFinite_endpoint_curvature_readouts (d : ℕ → ℝ)
    (A : ∀ m, RicciFlow 3 (U m) (Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)))
    (gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier) (DE : LeviCivitaData gE)
    (hendpoint : ∀ m (x : U m) (v w : E),
      ((A m).metric (-H.toReal)).inner x v w = gE.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w))
    (m : ℕ) (x : U m) :
    ((A m).connection (-H.toReal)).scalarCurvature x = DE.scalarCurvature x.val ∧
      (∀ v w z a : E, ((A m).connection (-H.toReal)).curvatureTensor x v w z a =
        DE.curvatureTensor x.val v w z a) ∧
      ((A m).connection (-H.toReal)).curvatureTensorNorm x = DE.curvatureTensorNorm x.val :=
  inclusion_curvature_readouts DE (U m) ((A m).connection (-H.toReal)) (hendpoint m) x

theorem limitFinite_endpoint_operator (d : ℕ → ℝ)
    (A : ∀ m, RicciFlow 3 (U m) (Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)))
    (gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier) (DE : LeviCivitaData gE)
    (hendpoint : ∀ m (x : U m) (v w : E),
      ((A m).metric (-H.toReal)).inner x v w = gE.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w))
    (hold : ∀ m t, t ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) →
      t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
        ((A m).metric t).inner x v w = (G.limit.flow.metric t).inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w))
    (hfinite : H ≠ ⊤) (hd : ∀ m, 0 < d m) :
    ∀ x, DE.NonnegativeCurvatureOperator x := by
  intro x
  have hx : x ∈ ⋃ m, G.exhaustion.space m := by
    rw [G.exhaustion.space_covers]
    exact mem_univ x
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  let y : U m := ⟨x, hm⟩
  have ht0 : -H.toReal ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) :=
    ⟨by linarith [hd m], by linarith [hd m]⟩
  apply DE.nonnegativeCurvatureOperator_of_nonnegative_sectional_three
    DE.intrinsicCurvatureTensorCalculus x
  intro v w
  have hcont := ((M04.contDiffOn_curvatureTensor_timeSlice (A m) y v w v w).continuousOn
    (-H.toReal) ht0).continuousAt (isOpen_Ioo.mem_nhds ht0)
  have hlim : Tendsto (fun t => ((A m).connection t).curvatureTensor y v w v w)
      (𝓝[>] (-H.toReal))
      (𝓝 (((A m).connection (-H.toReal)).curvatureTensor y v w v w)) :=
    hcont.mono_left nhdsWithin_le_nhds
  have hnonneg : ∀ᶠ t in 𝓝[>] (-H.toReal),
      0 ≤ ((A m).connection t).curvatureTensor y v w v w := by
    filter_upwards [old_right_tail G hfinite (hd m)] with t ht
    have hread := inclusion_curvature_readouts (G.limit.flow.connection t) (U m)
      ((A m).connection t) (hold m t ht.1 ht.2) y
    rw [hread.2.1]
    exact (G.limit.flow.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (G.limit.nonnegative_curvature_operator t ht.2 x) v w
  have hzero := ge_of_tendsto hlim hnonneg
  exact hzero.trans_eq
    ((limitFinite_endpoint_curvature_readouts G d A gE DE hendpoint m y).2.1 v w v w)

theorem limitFinite_endpoint_bounds (d : ℕ → ℝ)
    (A : ∀ m, RicciFlow 3 (U m) (Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)))
    (gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier) (DE : LeviCivitaData gE)
    (hendpoint : ∀ m (x : U m) (v w : E),
      ((A m).metric (-H.toReal)).inner x v w = gE.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w))
    (hold : ∀ m t, t ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) →
      t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
        ((A m).metric t).inner x v w = (G.limit.flow.metric t).inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w))
    (hfinite : H ≠ ⊤) (hd : ∀ m, 0 < d m)
    {X : Set G.limit.sliceCarrier.carrier} {K : ℝ}
    (hbound : ∀ t ∈ blowupBackwardInterval H, ∀ x ∈ X,
      (G.limit.flow.connection t).scalarCurvature x ≤ K ∧
        (G.limit.flow.connection t).curvatureTensorNorm x ≤ 9 * K) :
    ∀ x ∈ X, DE.scalarCurvature x ≤ K ∧ DE.curvatureTensorNorm x ≤ 9 * K := by
  intro x hxX
  have hx : x ∈ ⋃ m, G.exhaustion.space m := by
    rw [G.exhaustion.space_covers]
    exact mem_univ x
  obtain ⟨m, hm⟩ := mem_iUnion.mp hx
  let y : U m := ⟨x, hm⟩
  have ht0 : -H.toReal ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) :=
    ⟨by linarith [hd m], by linarith [hd m]⟩
  have htail : ∀ᶠ t in 𝓝[>] (-H.toReal),
      ((A m).connection t).scalarCurvature y ≤ K ∧
        ((A m).connection t).curvatureTensorNorm y ≤ 9 * K := by
    filter_upwards [old_right_tail G hfinite (hd m)] with t ht
    have hread := inclusion_curvature_readouts (G.limit.flow.connection t) (U m)
      ((A m).connection t) (hold m t ht.1 ht.2) y
    rw [hread.1, hread.2.2]
    exact hbound t ht.2 x hxX
  have hbound0 := curvature_bounds_of_right_limit (A m) isOpen_Ioo ht0 y htail
  have hread := limitFinite_endpoint_curvature_readouts G d A gE DE hendpoint m y
  exact ⟨hread.1.symm.trans_le hbound0.1, hread.2.2.symm.trans_le hbound0.2⟩

end PoincareConjecture.M47

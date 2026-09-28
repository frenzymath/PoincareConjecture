import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Slice
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Certificate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Extrema.FiniteRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [CompactSpace M] [Nonempty M] {g : RiemannianMetric 3 M}

theorem ricci_eq_scale_of_compact_round_soliton (D : LeviCivitaData g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) 2 f)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 3) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hround : ConstantPositiveSectionalCurvature g D)
    (x : M) (v w : TangentSpace (𝓡 3) x) :
    D.ricci x v w = lambda * g.inner x v w := by
  obtain ⟨c, _, hsec⟩ := hround
  have hRic (y : M) (a b : TangentSpace (𝓡 3) y) :
      D.ricci y a b = 2 * c * g.inner y a b := by
    have h := D.ricci_of_constant_sectional y c
      (D.sectionalCurvature_eq_of_orthonormal y c (hsec y)) a b
    norm_num at h
    exact h
  have hunit (y : M) : ∃ a : TangentSpace (𝓡 3) y, g.inner y a a = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let i : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) y)) := ⟨0, by simp [TangentSpace]⟩
    refine ⟨g.orthonormalBasis y i, ?_⟩
    change inner ℝ (g.orthonormalBasis y i) (g.orthonormalBasis y i) = 1
    simp
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuous.continuousOn
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuous.continuousOn
  obtain ⟨a, ha⟩ := hunit p
  obtain ⟨b, hb⟩ := hunit q
  have hmax := D.hessian_nonpos_of_isLocalMax_C2 hf (hp.isLocalMax (by simp)) a
  have hmin := D.hessian_nonneg_of_isLocalMin_C2 hf (hq.isLocalMin (by simp)) b
  have hp' := hsol p a a
  have hq' := hsol q b b
  rw [hRic, ha] at hp'
  rw [hRic, hb] at hq'
  have hc : 2 * c = lambda := by linarith
  rw [hRic, hc]

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem homotheticMetricSlice_of_ricci_scale (F : RicciFlow 3 M (Iio 0))
    (hRic : ∀ t : ℝ, t < 0 → ∀ x : M, ∀ u v : TangentSpace (𝓡 3) x,
      (F.connection t).ricci x u v = -(1 / (2 * t)) * (F.metric t).inner x u v)
    (t : ℝ) (ht : t < 0) :
    Nonempty (HomotheticMetricSlice (F.metric (-1)) (F.metric t) |t|) := by
  refine ⟨{ map := Diffeomorph.refl (𝓡 3) M ∞, inner_eq := ?_ }⟩
  intro x u v
  have hg (s : ℝ) (hs : s < 0) :
      HasDerivAt (fun z => (F.metric z).inner x u v) ((F.metric s).inner x u v / s) s := by
    have h := (F.equation s hs x u v).hasDerivAt (isOpen_Iio.mem_nhds hs)
    have hc : -2 * (F.connection s).ricci x u v = (F.metric s).inner x u v / s := by
      rw [hRic s hs]
      ring
    rwa [hc] at h
  have hq (s : ℝ) (hs : s < 0) :
      HasDerivAt (fun z => (F.metric z).inner x u v / (-z)) 0 s := by
    have h := (hg s hs).div (hasDerivAt_id s).neg (neg_ne_zero.mpr (ne_of_lt hs))
    have hc : ((F.metric s).inner x u v / s * (-s) -
        (F.metric s).inner x u v * (-1)) / (-s) ^ 2 = 0 := by
      field_simp [ne_of_lt hs]
      ring
    simp only [Pi.neg_apply, id_eq] at h
    rwa [hc] at h
  have heq := isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
    (fun s hs => (hq s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hq s hs).deriv) ht (show (-1 : ℝ) ∈ Iio 0 by norm_num)
  norm_num only [neg_neg, div_one] at heq
  have h := (div_eq_iff (neg_ne_zero.mpr (ne_of_lt ht))).mp heq
  simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id, ContinuousLinearMap.id_apply,
    abs_of_neg ht, mul_comm] using h

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem classificationCertificate_of_compact_round
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    [CompactSpace L.convergence.limit.carrier.carrier]
    (hround : ∀ t : ℝ, t < 0 →
      ConstantPositiveSectionalCurvature (L.convergence.limit.flow.metric t)
        (L.convergence.limit.flow.connection t)) :
    ThreeDimensionalAsymptoticClassificationCertificate S L := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  have hbound := L.convergence.limit.bounded_curvature_of_compact hC
  let S₀ := L.shrinkingSolitonData hC (hbound (-1) (by norm_num))
  have hRic (t : ℝ) (ht : t < 0) (x : L.convergence.limit.carrier.carrier)
      (v w : TangentSpace (𝓡 3) x) :
      (L.convergence.limit.flow.connection t).ricci x v w =
        -(1 / (2 * t)) * (L.convergence.limit.flow.metric t).inner x v w := by
    apply (L.convergence.limit.flow.connection t).ricci_eq_scale_of_compact_round_soliton
      ((L.contMDiff_potential_slice t ht).of_le (by norm_cast))
      (fun y a b => ?_) (hround t ht)
    have h := L.soliton_equation t ht y a b
    linarith
  let G : ShrinkingSolitonFlow S₀ :=
    { flow := L.convergence.limit.flow
      at_minus_one := rfl
      self_similar := fun t ht =>
        L.convergence.limit.flow.homotheticMetricSlice_of_ricci_scale hRic t ht }
  refine ⟨hbound, ?_⟩
  exact ⟨S₀, G, rfl, rfl, ⟨.compactRound ⟨inferInstance, hround⟩⟩⟩

end PoincareConjecture.AncientAsymptoticSolitonLimitData

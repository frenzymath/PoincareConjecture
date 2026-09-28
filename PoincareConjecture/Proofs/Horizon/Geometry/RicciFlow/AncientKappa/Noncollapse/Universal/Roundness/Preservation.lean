import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.LocalContinuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TransportedContact
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.LocalPreservation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Bundle Poincare.HamiltonIvey
open PoincareConjecture.RicciFlow.Frame
open scoped Manifold ContDiff Topology InnerProductSpace NNReal

namespace PoincareConjecture.AncientKappaRoundness

private theorem exists_uniform_lipschitzOnWith_tensorReaction
    {B : Type*} {V : B → Type*} [∀ x, NormedAddCommGroup (V x)]
    [∀ x, InnerProductSpace ℝ (V x)] [∀ x, FiniteDimensional ℝ (V x)]
    (hn : ∀ x, Module.finrank ℝ (V x) = 3) (R : ℝ) :
    ∃ C : ℝ≥0, ∀ x,
      LipschitzOnWith C (tensorReaction (E := V x)) (Metric.closedBall 0 R) := by
  obtain ⟨C, hC⟩ := exists_lipschitzOnWith_tensorReaction
    (E := EuclideanSpace ℝ (Fin 3)) (Metric.closedBall 0 R)
    (isCompact_closedBall 0 R) (convex_closedBall 0 R)
  refine ⟨C, fun x => ?_⟩
  let b : OrthonormalBasis (Fin 3) ℝ (V x) :=
    (stdOrthonormalBasis ℝ (V x)).reindex (finCongr (hn x))
  let e := TensorFiber.transport b.repr 2
  apply LipschitzOnWith.of_dist_le_mul
  intro T hT S hS
  have hT' : e T ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hT
  have hS' : e S ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hS
  have h := hC.dist_le_mul (e T) hT' (e S) hS'
  simpa only [e, tensorReaction_transport, LinearIsometryEquiv.dist_map] using h

variable {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {a b : ℝ}

local instance (x : M) : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
  unfold TangentSpace
  infer_instance

omit [T2Space M] [CompactSpace M] [IsManifold (𝓡 3) ∞ M] in
private theorem finrank_tangent (x : M) :
    Module.finrank ℝ (TangentSpace (𝓡 3) x) = 3 := by
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3
  simp

theorem transportedRicciComplement_mem_of_initial
    (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (hscalar : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (Ico a b ×ˢ univ))
    (hevolution : ∀ t ∈ Ico a b, ∀ x : M,
      ∀ u v w z : TangentSpace (𝓡 3) x,
      HasDerivWithinAt (fun s => (F.connection s).curvatureTensor x u v w z)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
          (F.connection t).curvatureReaction x u v w z) (Ico a b) t)
    {c : ℝ} (hc : 1 ≤ c)
    (hinit : ∀ x : M,
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨(F.metric a).toRiemannianMetric⟩
      (F.connection a).ricciComplementTensor (hcalculus a) x ∈ tensorPinchingCone c)
    {t : ℝ} (ht : t ∈ Ico a b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    transportedRicciComplement F hcalculus t x ∈ tensorPinchingCone c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  have hab : a < b := ht.1.trans_lt ht.2
  obtain ⟨O, hO, hpO, e, heK, hU⟩ :=
    exists_transportedRicciComplement_local_coordinates F hcalculus hscalar c ht.2
  have cmp := @Poincare.Parabolic.local_mem_of_inward_of_contact M _ _ _
    (fun y : M => TensorFiber (TangentSpace (𝓡 3) y) 2)
    (fun y => inferInstance) (fun y => inferInstance) (fun y => inferInstance)
    (fun _ => tensorPinchingCone c)
  have cmp' := @cmp
    (fun y => tensorPinchingCone_nonempty (E := TangentSpace (𝓡 3) y) c)
    (fun y => isClosed_tensorPinchingCone (E := TangentSpace (𝓡 3) y) c)
    (fun y => convex_tensorPinchingCone (E := TangentSpace (𝓡 3) y) c) O hO hpO e heK
  have cmp'' := @cmp'
    (fun y s => transportedRicciComplement F hcalculus s y)
    (fun y s => transportedRicciComplementDiffusion F hcalculus s y)
    (fun y _ => tensorReaction (E := TangentSpace (𝓡 3) y)) a t
  apply (cmp'' hU) ?_ ?_ ?_ ?_ ?_ x t ⟨ht.1, le_rfl⟩
  · intro y s hs
    exact (hasDerivAt_transportedRicciComplement F hcalculus hevolution
      ⟨hs.1, hs.2.trans_lt ht.2⟩ y).hasDerivWithinAt
  · intro R
    obtain ⟨C, hC⟩ := exists_uniform_lipschitzOnWith_tensorReaction
      (B := M) (V := (TangentSpace (𝓡 3) : M → Type _)) finrank_tangent R
    exact ⟨C, fun y _ _ => hC y⟩
  · intro y s hs q hq
    exact tensorReaction_inner_nonpos (finrank_tangent y) hc hq
  · intro y s hs q hq _ hactive hmax
    exact transportedRicciComplementDiffusion_nonpos_at_contact F hcalculus hab
      ⟨hs.1.le, hs.2.trans_lt ht.2⟩ y c q hq hactive (Filter.Eventually.of_forall hmax)
  · intro y
    have hinit_eq : transportedRicciComplement F hcalculus a y =
        (F.connection a).ricciComplementTensor (hcalculus a) y := by
      apply TensorFiber.ext
      intro v
      simp only [transportedRicciComplement_apply, canonicalTransport_initial F hab,
        ContinuousLinearMap.id_apply, LeviCivitaData.ricciComplementTensor_apply]
    rw [hinit_eq]
    exact hinit y

omit [T2Space M] [CompactSpace M] in
private theorem tensorPinchingCone_pullback_iff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : RiemannianMetric 3 M} (x : M)
    (e : E ≃ₗ[ℝ] TangentSpace (𝓡 3) x)
    (he : ∀ v w, g.inner x (e v) (e w) = inner ℝ v w)
    (T : TensorFiber (TangentSpace (𝓡 3) x) 2) (c : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    TensorFiber.toMultilinear.symm
        ((TensorFiber.toMultilinear T).compLinearMap (fun _ => e.toLinearMap)) ∈
          tensorPinchingCone c ↔ T ∈ tensorPinchingCone c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact tensorPinchingCone_transport_iff (e.isometryOfInner he).symm c T

theorem ricciComplement_mem_of_initial
    (F : RicciFlow 3 M (Ico a b))
    (hcalculus : ∀ s, (F.connection s).CurvatureTensorCalculus)
    (hscalar : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2) (Ico a b ×ˢ univ))
    (hevolution : ∀ t ∈ Ico a b, ∀ x : M,
      ∀ u v w z : TangentSpace (𝓡 3) x,
      HasDerivWithinAt (fun s => (F.connection s).curvatureTensor x u v w z)
        ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
          (F.connection t).curvatureReaction x u v w z) (Ico a b) t)
    {c : ℝ} (hc : 1 ≤ c)
    (hinit : ∀ x : M,
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨(F.metric a).toRiemannianMetric⟩
      (F.connection a).ricciComplementTensor (hcalculus a) x ∈ tensorPinchingCone c)
    {t : ℝ} (ht : t ∈ Ico a b) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F.metric t).toRiemannianMetric⟩
    (F.connection t).ricciComplementTensor (hcalculus t) x ∈ tensorPinchingCone c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  have hmem := transportedRicciComplement_mem_of_initial
    F hcalculus hscalar hevolution hc hinit ht x
  have hiff := tensorPinchingCone_pullback_iff (E := TangentSpace (𝓡 3) x) x
    (orthonormalTransport F t x).toLinearEquiv
    (canonicalTransport_pairing F (ht.1.trans_lt ht.2) ht x)
    ((F.connection t).ricciComplementTensor (hcalculus t) x) c
  exact hiff.mp hmem

end PoincareConjecture.AncientKappaRoundness

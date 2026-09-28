import PoincareConjecture.Proofs.M28.Generalized.StrongNeckGlobalBounds
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {F : GeneralizedRicciFlowData.{u}} {t epsilon : ℝ}
  (S : GeneralizedStrongNeck F t epsilon)
  (H : RescaledRawCylinderData (C := F.slice t)
    (U := strongNeckOpen S) (J := strongNeckBackwardInterval)
    (strongNeckCylinder S) (GeneralizedStrongNeck.physical_interval_subset S))
  (Q : ℝ) (hQ : 0 < Q) (tau : ℝ) (htau : 0 < tau)
  (hwindow : tau ≤ Q * S.scale ^ 2 / 4)
  (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U) [Nonempty U]
  (e : U → (F.slice t).carrier)
  (he : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ e)
  (hcapture : ∀ x, e x ∈ S.carrier)

def GeneralizedStrongNeck.captured_chart_map : U → strongNeckOpen S :=
  fun x => ⟨e x, hcapture x⟩

include he

theorem GeneralizedStrongNeck.captured_chart_map_localDiffeomorph :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (GeneralizedStrongNeck.captured_chart_map S U e hcapture) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  intro x
  let f := GeneralizedStrongNeck.captured_chart_map S U e hcapture
  have hi := openSubtype_isLocalDiffeomorph (strongNeckOpen S) (f x)
  have hinverse : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hi.localInverse (e x) :=
    hi.localInverse_isLocalDiffeomorphAt
  apply ((he x).comp (𝓡 3) (strongNeckOpen S) hinverse).congr_of_eventuallyEq
  filter_upwards [hi.localInverse_eventuallyEq_right.comp_tendsto
    (he x).contMDiffAt.continuousAt] with y hy
  apply Subtype.ext
  exact hy.symm

def GeneralizedStrongNeck.global_chart_flow :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    RicciFlow 3 U (Icc (-tau) 0) :=
  (GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).pullbackToCanonicalDomain
    U hU (GeneralizedStrongNeck.captured_chart_map S U e hcapture)
    (GeneralizedStrongNeck.captured_chart_map_localDiffeomorph S U hU e he hcapture)

theorem GeneralizedStrongNeck.global_chart_flow_metric_at_zero :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      ((GeneralizedStrongNeck.global_chart_flow S H Q hQ tau htau hwindow
        U hU e he hcapture).metric 0).inner x v w =
        Q * (F.metric t).inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
          (mfderiv (𝓡 3) (𝓡 3) e x w) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro x v w
  let f := GeneralizedStrongNeck.captured_chart_map S U e hcapture
  have hf := GeneralizedStrongNeck.captured_chart_map_localDiffeomorph S U hU e he hcapture
  have hderiv (z : TangentSpace (𝓡 3) x) :
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : strongNeckOpen S → (F.slice t).carrier)
          (f x) (mfderiv (𝓡 3) (𝓡 3) f x z) =
        mfderiv (𝓡 3) (𝓡 3) e x z := by
    exact (mfderiv_comp_apply x
      ((contMDiff_subtype_val (n := ∞) (f x)).mdifferentiableAt (by simp))
      ((hf x).mdifferentiableAt (by simp)) z).symm
  change ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).metric 0).inner
    (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) = _
  rw [GeneralizedStrongNeck.global_flow_metric_at_zero, hderiv, hderiv]
  rfl

theorem GeneralizedStrongNeck.global_chart_flow_curvatureTensorNorm :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ (s : ℝ) (x : U),
      ((GeneralizedStrongNeck.global_chart_flow S H Q hQ tau htau hwindow
        U hU e he hcapture).connection s).curvatureTensorNorm x =
        ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection
          s).curvatureTensorNorm
            (GeneralizedStrongNeck.captured_chart_map S U e hcapture x) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro s x
  let f := GeneralizedStrongNeck.captured_chart_map S U e hcapture
  have hf := GeneralizedStrongNeck.captured_chart_map_localDiffeomorph S U hU e he hcapture
  exact ((GeneralizedStrongNeck.global_chart_flow S H Q hQ tau htau hwindow
    U hU e he hcapture).connection s).curvatureTensorNorm_eq_of_local_isometry
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s)
      isOpen_univ hf.contMDiff.contMDiffOn (fun _ _ _ _ => rfl) (mem_univ x)

theorem GeneralizedStrongNeck.global_chart_flow_curvatureDerivativeNorm :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ (s : ℝ) (m : ℕ) (x : U),
      ((GeneralizedStrongNeck.global_chart_flow S H Q hQ tau htau hwindow
        U hU e he hcapture).connection s).curvatureDerivativeNorm m x =
        ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection
          s).curvatureDerivativeNorm m
            (GeneralizedStrongNeck.captured_chart_map S U e hcapture x) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro s m x
  let f := GeneralizedStrongNeck.captured_chart_map S U e hcapture
  have hf := GeneralizedStrongNeck.captured_chart_map_localDiffeomorph S U hU e he hcapture
  exact ((GeneralizedStrongNeck.global_chart_flow S H Q hQ tau htau hwindow
    U hU e he hcapture).connection s).curvatureDerivativeNorm_eq_pullback
      ((GeneralizedStrongNeck.global_flow S H Q hQ tau htau hwindow).connection s)
      isOpen_univ hf.contMDiff.contMDiffOn
      (fun y _ => ⟨(hf y).mfderivToContinuousLinearEquiv (by simp), rfl⟩)
      (fun _ _ _ _ => rfl) m (mem_univ x)

end PoincareConjecture.M28

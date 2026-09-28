import PoincareConjecture.Proofs.M03.Existence.MetricFamilyProducerNative
import PoincareConjecture.Proofs.M03.Existence.PullbackRicciNative

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.DeTurckPullbackSourceNative

open DiffeomorphNative DeTurckNative MetricFamilyProducerNative

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (g background : RiemannianMetric n M)
  (Phi : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)

local notation "E" => EuclideanSpace ℝ (Fin n)

def smoothPullbackMetric : RiemannianMetric n M :=
  pullbackMetric g Phi (contMDiff_pullback_section g Phi)

@[simp] theorem smoothPullbackMetric_inner (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    (smoothPullbackMetric g Phi).inner x v w =
      g.inner (Phi x) (mfderiv (𝓡 n) (𝓡 n) Phi x v)
        (mfderiv (𝓡 n) (𝓡 n) Phi x w) :=
  pullbackMetric_inner g Phi (contMDiff_pullback_section g Phi) x v w

theorem connectionDifference_pullback
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    (P : LeviCivitaData (smoothPullbackMetric g Phi))
    (Q : LeviCivitaData (smoothPullbackMetric background Phi))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    mfderiv (𝓡 n) (𝓡 n) Phi x
        (CovariantDerivative.difference P.connection Q.connection x u v) =
      CovariantDerivative.difference D.connection B.connection (Phi x)
        (mfderiv (𝓡 n) (𝓡 n) Phi x u) (mfderiv (𝓡 n) (𝓡 n) Phi x v) := by
  let Y : (y : M) → TangentSpace (𝓡 n) y :=
    FiberBundle.extend E (mfderiv (𝓡 n) (𝓡 n) Phi x u)
  have hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) (T% Y) (Phi x) :=
    FiberBundle.mdifferentiableAt_extend (𝓡 n) E _
  have hYx : Y (Phi x) = mfderiv (𝓡 n) (𝓡 n) Phi x u :=
    FiberBundle.extend_apply_self E _
  have hpY : pullField Phi Y x = u := by
    apply (Phi.mfderivToContinuousLinearEquiv (by simp) x).injective
    change mfderiv (𝓡 n) (𝓡 n) Phi x (pullField Phi Y x) =
      mfderiv (𝓡 n) (𝓡 n) Phi x u
    exact (mfderiv_pullField Phi Y x).trans hYx
  calc
    _ = mfderiv (𝓡 n) (𝓡 n) Phi x
        (P.connection (pullField Phi Y) x v - Q.connection (pullField Phi Y) x v) := by
      rw [← hpY, connectionDifference_apply_field P Q (mdifferentiableAt_pullField Phi hY)]
    _ = D.connection Y (Phi x) (mfderiv (𝓡 n) (𝓡 n) Phi x v) -
        B.connection Y (Phi x) (mfderiv (𝓡 n) (𝓡 n) Phi x v) := by
      rw [map_sub,
        connection_pullField_apply g Phi (contMDiff_pullback_section g Phi) D P Y hY v,
        connection_pullField_apply background Phi (contMDiff_pullback_section background Phi)
          B Q Y hY v]
    _ = _ := by
      rw [← connectionDifference_apply_field D B hY, hYx]

theorem intrinsicDeTurckField_pullback
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    (P : LeviCivitaData (smoothPullbackMetric g Phi))
    (Q : LeviCivitaData (smoothPullbackMetric background Phi)) (x : M) :
    mfderiv (𝓡 n) (𝓡 n) Phi x (intrinsicDeTurckField P Q x) =
      intrinsicDeTurckField D B (Phi x) := by
  let A := Phi.mfderivToContinuousLinearEquiv (by simp) x
  let b := chartFrameBasis x x (mem_chart_source E x)
  let b' := b.map A.toLinearEquiv
  let F (i : Fin n) : (y : M) → TangentSpace (𝓡 n) y := FiberBundle.extend E (b i)
  let G (i : Fin n) : (y : M) → TangentSpace (𝓡 n) y := FiberBundle.extend E (b' i)
  have hF (i : Fin n) : F i x = b i := FiberBundle.extend_apply_self E _
  have hG (i : Fin n) : G i (Phi x) = b' i := FiberBundle.extend_apply_self E _
  have hFG (i : Fin n) : mfderiv (𝓡 n) (𝓡 n) Phi x (F i x) = G i (Phi x) := by
    rw [hF, hG]
    change mfderiv (𝓡 n) (𝓡 n) Phi x (b i) = A (b i)
    exact (congrArg (fun L => L (b i))
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe Phi (by simp) (x := x))).symm
  have hgram : (frameMetricJet (smoothPullbackMetric g Phi) F x).value =
      (frameMetricJet g G (Phi x)).value := by
    ext i j
    change (smoothPullbackMetric g Phi).inner x (F i x) (F j x) =
      g.inner (Phi x) (G i (Phi x)) (G j (Phi x))
    rw [smoothPullbackMetric_inner, hFG, hFG]
  rw [intrinsicDeTurckField_eq_frame_contraction P Q F x b hF,
    intrinsicDeTurckField_eq_frame_contraction D B G (Phi x) b' hG]
  simp only [map_sum, map_smul, hgram]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [connectionDifference_pullback g background Phi D B P Q x, hFG, hFG]

theorem intrinsicDeTurckField_eq_pullField
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    (P : LeviCivitaData (smoothPullbackMetric g Phi))
    (Q : LeviCivitaData (smoothPullbackMetric background Phi)) :
    intrinsicDeTurckField P Q = pullField Phi (intrinsicDeTurckField D B) := by
  funext x
  apply (Phi.mfderivToContinuousLinearEquiv (by simp) x).injective
  change mfderiv (𝓡 n) (𝓡 n) Phi x (intrinsicDeTurckField P Q x) =
    mfderiv (𝓡 n) (𝓡 n) Phi x (pullField Phi (intrinsicDeTurckField D B) x)
  rw [mfderiv_pullField]
  exact intrinsicDeTurckField_pullback g background Phi D B P Q x

theorem metricLieDerivative_pullback (D : LeviCivitaData g)
    (P : LeviCivitaData (smoothPullbackMetric g Phi))
    (W : (y : M) → TangentSpace (𝓡 n) y)
    (hW : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% W))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    metricLieDerivative P (pullField Phi W) x u v =
      metricLieDerivative D W (Phi x)
        (mfderiv (𝓡 n) (𝓡 n) Phi x u) (mfderiv (𝓡 n) (𝓡 n) Phi x v) := by
  rw [metricLieDerivative_apply, metricLieDerivative_apply,
    smoothPullbackMetric_inner, smoothPullbackMetric_inner,
    connection_pullField_apply g Phi (contMDiff_pullback_section g Phi) D P W
      (hW.mdifferentiable (by simp) (Phi x)) u,
    connection_pullField_apply g Phi (contMDiff_pullback_section g Phi) D P W
      (hW.mdifferentiable (by simp) (Phi x)) v]

theorem smoothRicciDeTurckTensor_pullback
    (D : LeviCivitaData g) (B : LeviCivitaData background)
    (P : LeviCivitaData (smoothPullbackMetric g Phi))
    (Q : LeviCivitaData (smoothPullbackMetric background Phi))
    (x : M) (u v : TangentSpace (𝓡 n) x) :
    smoothRicciDeTurckTensor P Q x u v =
      smoothRicciDeTurckTensor D B (Phi x)
        (mfderiv (𝓡 n) (𝓡 n) Phi x u) (mfderiv (𝓡 n) (𝓡 n) Phi x v) := by
  rw [smoothRicciDeTurckTensor_apply, smoothRicciDeTurckTensor_apply,
    intrinsicDeTurckField_eq_pullField g background Phi D B P Q,
    metricLieDerivative_pullback g Phi D P (intrinsicDeTurckField D B)
      (intrinsicDeTurckField_contMDiff D B),
    ricci_pullback g Phi (contMDiff_pullback_section g Phi) D P]

end PoincareConjecture.DeTurckPullbackSourceNative

end

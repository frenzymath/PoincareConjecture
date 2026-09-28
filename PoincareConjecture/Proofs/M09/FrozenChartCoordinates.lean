import PoincareConjecture.Proofs.M09.ChartConnectionLocal
import PoincareConjecture.Proofs.M09.SmoothTangentChartPhase
import PoincareConjecture.Proofs.M09.ChartVelocity
import PoincareConjecture.Proofs.M09.CompactFieldExtension








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def frozenChartCoordinates (p q : M) (v : TangentSpace (𝓡 n) q) : M → E :=
  fun x ↦ mfderiv (𝓡 n) (𝓡 n) (chartAt E p) x (FiberBundle.extend E v x)

theorem frozenChartCoordinates_contMDiffAt (p q : M) (hq : q ∈ (chartAt E p).source)
    (v : TangentSpace (𝓡 n) q) :
    ContMDiffAt (𝓡 n) (𝓡 n) ∞ (frozenChartCoordinates p q v) q := by
  have he : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (FiberBundle.extend E v)) q := FiberBundle.contMDiffAt_extend (𝓡 n) E v
  have ht := (tangentChartPhase_contMDiffOn p).contMDiffAt
    (((chartAt E p).open_source.preimage
      (FiberBundle.continuous_proj E (TangentSpace (𝓡 n)))).mem_nhds
      (show (⟨q, FiberBundle.extend E v q⟩ : TangentBundle (𝓡 n) M).proj ∈
        (chartAt E p).source from hq))
  exact (ContinuousLinearMap.snd ℝ E E).contMDiff.contMDiffAt.comp q (ht.comp q he)

theorem frozenChartCoordinates_reconstruct (p q x : M) (v : TangentSpace (𝓡 n) q)
    (hx : x ∈ (chartAt E p).source) :
    chartVectorField p (frozenChartCoordinates p q v x) x = FiberBundle.extend E v x :=
  chartVectorField_differential p x (FiberBundle.extend E v x) hx

theorem frozenChartCoordinates_at_base (p q : M) (hq : q ∈ (chartAt E p).source)
    (v : E) : frozenChartCoordinates p q (chartVectorField p v q) q = v := by
  have hi : (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) q).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv hq, rfl⟩
  unfold frozenChartCoordinates
  rw [FiberBundle.extend_apply_self]
  exact hi.self_apply_inverse v

theorem connection_frozenChartCoordinates {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (p q : M) (hq : q ∈ (chartAt E p).source)
    (X : TangentSpace (𝓡 n) q) (A : E →L[ℝ] E)
    (hA : ∀ v : E, D.connection (chartVectorField p v) q X = chartVectorField p (A v) q)
    (v : E) :
    D.connection (FiberBundle.extend E (chartVectorField p v q)) q X =
      chartVectorField p (A v +
        mvfderiv (𝓡 n) (frozenChartCoordinates p q (chartVectorField p v q)) q X) q := by
  have h := connection_of_eventuallyEq_chartVectorField_on_source D p q hq
    (frozenChartCoordinates p q (chartVectorField p v q))
    ((frozenChartCoordinates_contMDiffAt p q hq _).mdifferentiableAt (by simp))
    (FiberBundle.extend E (chartVectorField p v q)) (by
      filter_upwards [(chartAt E p).open_source.mem_nhds hq] with x hx
      exact (frozenChartCoordinates_reconstruct p q x _ hx).symm) X A hA
  rwa [frozenChartCoordinates_at_base p q hq] at h

end PoincareConjecture.Proofs.M09

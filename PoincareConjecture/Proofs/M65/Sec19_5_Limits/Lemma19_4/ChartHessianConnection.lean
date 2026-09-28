import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussTransport
import PoincareConjecture.Proofs.M62.Sec19_1_PullbackTorsion











set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set Filter VectorField
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M65Gauss

open Proofs.M09

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}
  {gE : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}




theorem connection_chartVectorField
    (D : LeviCivitaData g) (DE : LeviCivitaData gE) (p : M)
    {q : EuclideanSpace ℝ (Fin n)}
    (hq : q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).target)
    (hmetric : ∀ᶠ y in 𝓝 q, ∀ a b : EuclideanSpace ℝ (Fin n),
      gE.inner y a b = g.inner ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y a)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm y b))
    (a b : EuclideanSpace ℝ (Fin n)) :
    D.connection (chartVectorField p b) ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm q)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm q a) =
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm q
        (connectionCoefficient DE q a b) := by
  let c := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hψ : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm q :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds hq)
  have hinv (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).symm.mfderiv hy, rfl⟩
  have hinv' : ∀ᶠ y in 𝓝 q, (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    filter_upwards [c.open_target.mem_nhds hq] with y hy
    exact hinv y hy
  have hW : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (T% (chartVectorField p b)) (c.symm q) :=
    ((chartVectorField_smooth p b).contMDiffAt
      (c.open_source.mem_nhds (c.map_target hq))).mdifferentiableAt (by simp)
  have heq : mpullback (𝓡 n) (𝓡 n) c.symm (chartVectorField p b) =ᶠ[𝓝 q]
      (fun _ => b) := by
    filter_upwards [c.open_target.mem_nhds hq] with y hy
    rw [mpullback_apply, chartVectorField_at_inverse p b y hy]
    exact (hinv y hy).inverse_apply_self b
  have hP : DifferentiableAt ℝ
      (mpullback (𝓡 n) (𝓡 n) c.symm (chartVectorField p b)) q :=
    (differentiableAt_const b).congr_of_eventuallyEq heq
  have hleft : DE.connection (mpullback (𝓡 n) (𝓡 n) c.symm (chartVectorField p b)) q a =
      connectionCoefficient DE q a b := by
    rw [DE.connection_eq_fderiv_add hP, heq.fderiv_eq]
    simp only [fderiv_const_apply, zero_apply, zero_add, heq.self_of_nhds,
      connectionCoefficient_apply]
  have h := DE.connection_mpullback_of_metric_pullback D hψ hinv' hmetric hW a
  rw [hleft] at h
  have hpush := congrArg (mfderiv (𝓡 n) (𝓡 n) c.symm q) h
  simpa only [(hinv q hq).self_apply_inverse] using hpush.symm

end PoincareConjecture.M65Gauss

import PoincareConjecture.Proofs.M09.CenteredCoordinateDifferential









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

set_option backward.isDefEq.respectTransparency false in
theorem hessian_centeredCoordinates {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : M → ℝ) (p : M)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (chartAt E p).source)
    (U V : TangentSpace (𝓡 n) p) :
    let φ : E → ℝ := fun y ↦ f ((chartAt E p).symm y)
    D.hessian f p U V = fderiv ℝ (fun y ↦ fderiv ℝ φ y V) ((chartAt E p) p) U -
      fderiv ℝ φ ((chartAt E p) p) (D.connection (chartVectorField p V) p U) := by
  let φ : E → ℝ := fun y ↦ f ((chartAt E p).symm y)
  let ψ : E → ℝ := fun y ↦ fderiv ℝ φ y V
  have hφ : ContDiffOn ℝ ∞ φ (chartAt E p).target :=
    (hf.comp contMDiffOn_chart_symm (fun y hy ↦ (chartAt E p).map_target hy)).contDiffOn
  have hψ : ContDiffOn ℝ ∞ ψ (chartAt E p).target :=
    (hφ.fderiv_of_isOpen (chartAt E p).open_target (by simp)).clm_apply contDiffOn_const
  have hp : (chartAt E p) p ∈ (chartAt E p).target :=
    (chartAt E p).map_source (mem_chart_source E p)
  have heq : f =ᶠ[𝓝 p] (fun q ↦ φ ((chartAt E p) q)) := by
    filter_upwards [(chartAt E p).open_source.mem_nhds (mem_chart_source E p)] with q hq
    exact congrArg f ((chartAt E p).left_inv hq).symm
  have hinner : (fun q ↦ mvfderiv (𝓡 n) f q (chartVectorField p V q)) =ᶠ[𝓝 p]
      (fun q ↦ ψ ((chartAt E p) q)) := by
    filter_upwards [(chartAt E p).open_source.mem_nhds (mem_chart_source E p)] with q hq
    have hdiff : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f
        ((chartAt E p).symm ((chartAt E p) q)) := by
      rw [(chartAt E p).left_inv hq]
      exact (hf.contMDiffAt ((chartAt E p).open_source.mem_nhds hq)).mdifferentiableAt (by simp)
    have h := mvfderiv_chartVectorField p f ((chartAt E p) q) V
      ((chartAt E p).map_source hq) hdiff
    convert! h using 1
    rw [(chartAt E p).left_inv hq]
  have hfirst := mvfderiv_centeredChart_of_eventuallyEq p
    (fun q ↦ mvfderiv (𝓡 n) f q (chartVectorField p V q)) ψ
    ((hψ.contDiffAt ((chartAt E p).open_target.mem_nhds hp)).differentiableAt (by simp)) hinner U
  have hsecond := mvfderiv_centeredChart_of_eventuallyEq p f φ
    ((hφ.contDiffAt ((chartAt E p).open_target.mem_nhds hp)).differentiableAt (by simp)) heq
    (D.connection (chartVectorField p V) p U)
  rw [hessian_centeredChart, LeviCivitaData.hessianOnFields, chartVectorField_self,
    hfirst, hsecond]

end PoincareConjecture.Proofs.M09

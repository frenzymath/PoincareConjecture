import PoincareConjecture.Proofs.M09.CenteredHessian








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
theorem hessian_centeredCoordinates_local {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : M → ℝ) (p : M) (O : Set M)
    (hO : IsOpen O) (hpO : p ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (U W : TangentSpace (𝓡 n) p) :
    let φ : E → ℝ := fun y ↦ f ((chartAt E p).symm y)
    D.hessian f p U W = fderiv ℝ (fun y ↦ fderiv ℝ φ y W) ((chartAt E p) p) U -
      fderiv ℝ φ ((chartAt E p) p) (D.connection (chartVectorField p W) p U) := by
  let e := chartAt E p
  let V := e.target ∩ e.symm ⁻¹' O
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hV : IsOpen V := he.continuousOn.isOpen_inter_preimage e.open_target hO
  have hp : e p ∈ V := ⟨e.map_source (mem_chart_source E p), by
    change e.symm (e p) ∈ O
    rwa [e.left_inv (mem_chart_source E p)]⟩
  let φ : E → ℝ := fun y ↦ f (e.symm y)
  let ψ : E → ℝ := fun y ↦ fderiv ℝ φ y W
  have hφ : ContDiffOn ℝ ∞ φ V :=
    (hf.comp (he.mono Set.inter_subset_left) (fun y hy ↦ hy.2)).contDiffOn
  have hψ : ContDiffOn ℝ ∞ ψ V :=
    (hφ.fderiv_of_isOpen hV (by simp)).clm_apply contDiffOn_const
  have heq : f =ᶠ[𝓝 p] (fun q ↦ φ (e q)) := by
    filter_upwards [e.open_source.mem_nhds (mem_chart_source E p)] with q hq
    exact congrArg f (e.left_inv hq).symm
  have hinner : (fun q ↦ mvfderiv (𝓡 n) f q (chartVectorField p W q)) =ᶠ[𝓝 p]
      (fun q ↦ ψ (e q)) := by
    filter_upwards [(hO.inter e.open_source).mem_nhds ⟨hpO, mem_chart_source E p⟩] with q hq
    have hdiff : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f (e.symm (e q)) := by
      rw [e.left_inv hq.2]
      exact (hf.contMDiffAt (hO.mem_nhds hq.1)).mdifferentiableAt (by simp)
    have h := mvfderiv_chartVectorField p f (e q) W (e.map_source hq.2) hdiff
    convert! h using 1
    rw [e.left_inv hq.2]
  have hfirst := mvfderiv_centeredChart_of_eventuallyEq p
    (fun q ↦ mvfderiv (𝓡 n) f q (chartVectorField p W q)) ψ
    ((hψ.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)) hinner U
  have hsecond := mvfderiv_centeredChart_of_eventuallyEq p f φ
    ((hφ.contDiffAt (hV.mem_nhds hp)).differentiableAt (by simp)) heq
    (D.connection (chartVectorField p W) p U)
  rw [hessian_centeredChart, LeviCivitaData.hessianOnFields, chartVectorField_self,
    hfirst, hsecond]

end PoincareConjecture.Proofs.M09

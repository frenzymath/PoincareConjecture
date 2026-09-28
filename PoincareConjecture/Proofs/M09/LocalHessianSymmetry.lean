import PoincareConjecture.Proofs.M09.LocalHessianTrace
import PoincareConjecture.Proofs.M09.CoordinateCompatibility
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareTime_hessian_symmetric_local {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (f : M → ℝ) (O : Set M) (hO : IsOpen O) (hpO : p ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (v w : TangentSpace (𝓡 n) p) :
    (F.connection (T - s ^ 2)).hessian f p v w =
      (F.connection (T - s ^ 2)).hessian f p w v := by
  let e := chartAt E p
  let φ : E → ℝ := fun y ↦ f (e.symm y)
  let V := e.target ∩ e.symm ⁻¹' O
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hV : IsOpen V := he.continuousOn.isOpen_inter_preimage e.open_target hO
  have hy : e p ∈ V := ⟨e.map_source (mem_chart_source E p), by
    change e.symm (e p) ∈ O
    rwa [e.left_inv (mem_chart_source E p)]⟩
  have hφ : ContDiffAt ℝ ∞ φ (e p) :=
    ((hf.comp (he.mono Set.inter_subset_left) (fun y hy ↦ hy.2)).contDiffOn).contDiffAt
      (hV.mem_nhds hy)
  have hD := ((hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
  have hd (u z : E) : fderiv ℝ (fun y ↦ fderiv ℝ φ y z) (e p) u =
      fderiv ℝ (fderiv ℝ φ) (e p) u z := by
    have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const z (e p))
    simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L u) h.fderiv
  have hG : DifferentiableAt ℝ (squareChartMetric F T p) (s, e p) :=
    ((squareChartMetric_smooth F T b hb hwindow p).contDiffAt
      ((isOpen_Ioo.prod e.open_target).mem_nhds ⟨hs, e.map_source (mem_chart_source E p)⟩)).differentiableAt
        (by simp)
  have hconn := coordinateConnection_symm (squareChartMetric F T p) (s, e p) hG
    (Filter.Eventually.of_forall fun z ↦ squareChartMetric_symm F T p z) v w
  rw [hessian_centeredCoordinates_local (F.connection (T - s ^ 2)) f p O hO hpO hf v w,
    hessian_centeredCoordinates_local (F.connection (T - s ^ 2)) f p O hO hpO hf w v]
  change fderiv ℝ (fun y ↦ fderiv ℝ φ y w) (e p) v - _ =
    fderiv ℝ (fun y ↦ fderiv ℝ φ y v) (e p) w - _
  rw [hd v w, hd w v, ← squareChartConnection_at_center F T b hb hwindow p s hs v w,
    ← squareChartConnection_at_center F T b hb hwindow p s hs w v, hconn]
  congr 1
  have htwo : (2 : ℕ∞ω) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  exact hφ.isSymmSndFDerivAt (by simpa using htwo) v w

end PoincareConjecture.Proofs.M09

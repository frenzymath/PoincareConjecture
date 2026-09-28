import PoincareConjecture.Proofs.M09.LocalCenteredHessian
import PoincareConjecture.Proofs.M09.SecondDerivativeComposition
import PoincareConjecture.Proofs.M09.ChartFieldDerivative
import PoincareConjecture.Proofs.M09.VelocityRestriction
import PoincareConjecture.Proofs.M09.ChartVelocity

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

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem secondDeriv_comp_eq_hessian_add_acceleration {J : Set ℝ}
    (F : RicciFlow n M J) (t0 : ℝ) (γ : ℝ → M) (I : Set ℝ)
    (hI : IsOpen I) (hγ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ I)
    (H : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin γ I))
    (s : ℝ) (hs : s ∈ I) (f : M → ℝ) (O : Set M) (hO : IsOpen O)
    (hpO : γ s ∈ O) (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O) :
    deriv (deriv (fun r ↦ f (γ r))) s =
      (F.connection t0).hessian f (γ s) (curveVelocity γ s) (curveVelocity γ s) +
        mvfderiv (𝓡 n) f (γ s)
          (pullbackCovariantDerivative F (fun _ ↦ t0) γ (curveVelocityWithin γ I) I H s) := by
  let p := γ s
  let e := chartAt E p
  let W := I ∩ γ ⁻¹' e.source
  have hW : IsOpen W := hγ.continuousOn.isOpen_inter_preimage hI e.open_source
  have hsW : s ∈ W := ⟨hs, mem_chart_source E p⟩
  let y : ℝ → E := fun r ↦ e (γ r)
  have hy : ContDiffOn ℝ ∞ y W :=
    (contMDiffOn_chart.comp (hγ.mono Set.inter_subset_left) (fun r hr ↦ hr.2)).contDiffOn
  have hdy : ContDiffOn ℝ ∞ (deriv y) W := hy.deriv_of_isOpen hW (by simp)
  have hγd (r : ℝ) (hr : r ∈ I) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ r :=
    (hγ.contMDiffAt (hI.mem_nhds hr)).mdifferentiableAt (by simp)
  have hyd (r : ℝ) (hr : r ∈ W) : HasDerivAt y (deriv y r) r :=
    ((hy.contDiffAt (hW.mem_nhds hr)).differentiableAt (by simp)).hasDerivAt
  have hrep : ∀ r ∈ I ∩ W,
      chartVectorField p (deriv y r) (γ r) = curveVelocityWithin (n := n) γ I r := by
    intro r hr
    exact (chartVectorField_coordinate_velocity p γ r (deriv y r) hr.2.2
      (hγd r hr.1) (hyd r hr.2)).trans
      (curveVelocityWithin_eq_curveVelocity γ I r (hI.uniqueDiffOn r hr.1) (hγd r hr.1)).symm
  have hys : deriv y s = curveVelocity (n := n) γ s := by
    have h := (hasDerivAt_chart_curve p γ s hsW.2 (hγd s hs)).deriv
    change deriv y s = mfderiv (𝓡 n) (𝓡 n) e p (curveVelocity γ s) at h
    rw [show e = chartAt E p from rfl, mfderiv_chartAt_self] at h
    exact h
  have hvel := curveVelocityWithin_eq_curveVelocity γ I s (hI.uniqueDiffOn s hs) (hγd s hs)
  have hpull := pullbackCovariantDerivative_chart_field_local F (fun _ ↦ t0) p γ
    (curveVelocityWithin (n := n) γ I) I W H s hs hW hsW (hI.uniqueDiffOn s hs)
    (hγd s hs) (deriv y) hdy (fun r hr ↦ hr.2.2) hrep (deriv (deriv y) s)
    (((hdy.contDiffAt (hW.mem_nhds hsW)).differentiableAt (by simp)).hasDerivAt)
  rw [hvel, hys] at hpull
  change pullbackCovariantDerivative F (fun _ ↦ t0) γ (curveVelocityWithin γ I) I H s =
    chartVectorField p (deriv (deriv y) s) p +
      (F.connection t0).connection (chartVectorField p (curveVelocity γ s)) p
        (curveVelocity γ s) at hpull
  rw [chartVectorField_self] at hpull
  let V := e.target ∩ e.symm ⁻¹' O
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hV : IsOpen V := he.continuousOn.isOpen_inter_preimage e.open_target hO
  have hpV : e p ∈ V := ⟨e.map_source (mem_chart_source E p), by
    change e.symm (e p) ∈ O
    rwa [e.left_inv (mem_chart_source E p)]⟩
  let φ : E → ℝ := fun z ↦ f (e.symm z)
  have hφ : ContDiffOn ℝ ∞ φ V :=
    (hf.comp (he.mono Set.inter_subset_left) (fun z hz ↦ hz.2)).contDiffOn
  have hφat : ContDiffAt ℝ ∞ φ (e p) := hφ.contDiffAt (hV.mem_nhds hpV)
  have heq : f =ᶠ[𝓝 p] (fun q ↦ φ (e q)) := by
    filter_upwards [e.open_source.mem_nhds (mem_chart_source E p)] with q hq
    exact congrArg f (e.left_inv hq).symm
  have hfirst (v : E) : mvfderiv (𝓡 n) f p v = fderiv ℝ φ (e p) v :=
    mvfderiv_centeredChart_of_eventuallyEq p f φ
      (hφat.differentiableAt (by simp)) heq v
  have hDφ : DifferentiableAt ℝ (fderiv ℝ φ) (e p) :=
    (hφat.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have heval (v : E) : fderiv ℝ (fun z ↦ fderiv ℝ φ z v) (e p) v =
      fderiv ℝ (fderiv ℝ φ) (e p) v v := by
    simpa using congrArg (fun L : E →L[ℝ] ℝ ↦ L v)
      (hDφ.hasFDerivAt.clm_apply (hasFDerivAt_const v (e p))).fderiv
  have hH := hessian_centeredCoordinates_local (F.connection t0) f p O hO hpO hf
    (curveVelocity γ s) (curveVelocity γ s)
  change (F.connection t0).hessian f p (curveVelocity γ s) (curveVelocity γ s) =
    fderiv ℝ (fun z ↦ fderiv ℝ φ z (curveVelocity γ s)) (e p) (curveVelocity γ s) -
      fderiv ℝ φ (e p) ((F.connection t0).connection
        (chartVectorField p (curveVelocity γ s)) p (curveVelocity γ s)) at hH
  rw [heval] at hH
  have hcurve : (fun r ↦ f (γ r)) =ᶠ[𝓝 s] (fun r ↦ φ (y r)) := by
    filter_upwards [hW.mem_nhds hsW] with r hr
    exact congrArg f (e.left_inv hr.2).symm
  rw [hcurve.deriv.deriv_eq, secondDeriv_comp φ y s hφat (hy.contDiffAt (hW.mem_nhds hsW)),
    hys, hH, hfirst, hpull, map_add]
  ring

end PoincareConjecture.Proofs.M09

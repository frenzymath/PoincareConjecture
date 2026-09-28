import PoincareConjecture.Proofs.M09.FixedChartHessian








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

theorem hessian_eq_of_eventuallyEq {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f h : M → ℝ) (q : M)
    (heq : f =ᶠ[𝓝 q] h) (u v : TangentSpace (𝓡 n) q) :
    D.hessian f q u v = D.hessian h q u v := by
  have hcongr (f h : M → ℝ) (x : M) (hh : f =ᶠ[𝓝 x] h) :
      mvfderiv (𝓡 n) f x = mvfderiv (𝓡 n) h x := by
    unfold mvfderiv
    rw [hh.eq_of_nhds, hh.mfderiv_eq]
  have hfirst : (fun x ↦ mvfderiv (𝓡 n) f x (FiberBundle.extend E v x)) =ᶠ[𝓝 q]
      (fun x ↦ mvfderiv (𝓡 n) h x (FiberBundle.extend E v x)) := by
    filter_upwards [heq.eventuallyEq_nhds] with x hx
    rw [hcongr f h x hx]
  unfold LeviCivitaData.hessian LeviCivitaData.hessianOnFields
  change mvfderiv (𝓡 n) _ q _ - mvfderiv (𝓡 n) f q _ =
    mvfderiv (𝓡 n) _ q _ - mvfderiv (𝓡 n) h q _
  rw [hcongr _ _ q hfirst, hcongr f h q heq]

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hessian_fixedChart_local {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (f : M → ℝ) (p q : M) (hq : q ∈ (chartAt E p).source)
    (O : Set M) (hO : IsOpen O) (hqO : q ∈ O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (u v : E) (A : E →L[ℝ] E)
    (hA : ∀ w : E, D.connection (chartVectorField p w) q (chartVectorField p u q) =
      chartVectorField p (A w) q) :
    let φ : E → ℝ := fun y ↦ f ((chartAt E p).symm y)
    D.hessian f q (chartVectorField p u q) (chartVectorField p v q) =
      fderiv ℝ (fderiv ℝ φ) ((chartAt E p) q) u v -
        fderiv ℝ φ ((chartAt E p) q) (A v) := by
  dsimp only
  let e := chartAt E p
  let U := O ∩ e.source
  let V := e.target ∩ e.symm ⁻¹' O
  have hU : IsOpen U := hO.inter e.open_source
  have hqU : q ∈ U := ⟨hqO, hq⟩
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hV : IsOpen V := he.continuousOn.isOpen_inter_preimage e.open_target hO
  have hqV : e q ∈ V := ⟨e.map_source hq, by
    change e.symm (e q) ∈ O
    rwa [e.left_inv hq]⟩
  let φ : E → ℝ := fun y ↦ f (e.symm y)
  let P : M → E →L[ℝ] ℝ := fun x ↦ fderiv ℝ φ (e x)
  let X := chartVectorField p u q
  let Vq := chartVectorField p v q
  let c := frozenChartCoordinates p q Vq
  have hφ : ContDiffOn ℝ ∞ φ V :=
    (hf.comp (he.mono Set.inter_subset_left) (fun y hy ↦ hy.2)).contDiffOn
  have hDφ := hφ.fderiv_of_isOpen hV (m := ∞) (by simp)
  have hP : ContMDiffOn (𝓡 n) (𝓘(ℝ, E →L[ℝ] ℝ)) ∞ P U :=
    hDφ.contMDiffOn.comp (contMDiffOn_chart.mono Set.inter_subset_right) (by
      intro x hx
      exact ⟨e.map_source hx.2, by
        change e.symm (e x) ∈ O
        rw [e.left_inv hx.2]
        exact hx.1⟩)
  have hPd := (hP.contMDiffAt (hU.mem_nhds hqU)).mdifferentiableAt (by simp)
  have hcd := (frozenChartCoordinates_contMDiffAt p q hq Vq).mdifferentiableAt (by simp)
  have hcv : c q = v := frozenChartCoordinates_at_base p q hq v
  have hfirst (x : M) (hx : x ∈ U) (w : E) :
      mvfderiv (𝓡 n) f x (chartVectorField p w x) = P x w := by
    have hfx : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f (e.symm (e x)) := by
      rw [e.left_inv hx.2]
      exact (hf.contMDiffAt (hO.mem_nhds hx.1)).mdifferentiableAt (by simp)
    have h := mvfderiv_chartVectorField_normed p f (e x) w (e.map_source hx.2) hfx
    rwa [e.left_inv hx.2] at h
  have heq : (fun x ↦ mvfderiv (𝓡 n) f x (FiberBundle.extend E Vq x)) =ᶠ[𝓝 q]
      (fun x ↦ P x (c x)) := by
    filter_upwards [hU.mem_nhds hqU] with x hx
    rw [← frozenChartCoordinates_reconstruct p q x Vq hx.2]
    exact hfirst x hx (c x)
  have hder : mvfderiv (𝓡 n)
      (fun x ↦ mvfderiv (𝓡 n) f x (FiberBundle.extend E Vq x)) q X =
        P q (mvfderiv (𝓡 n) c q X) + mvfderiv (𝓡 n) P q X v := by
    rw [mvfderiv, heq.mfderiv_eq]
    change mvfderiv (𝓡 n) (fun x ↦ P x (c x)) q X = _
    rw [mvfderiv_clm_application P c q hPd hcd X, hcv]
  have hPder : mvfderiv (𝓡 n) P q X = fderiv ℝ (fderiv ℝ φ) (e q) u := by
    have hPd' : MDifferentiableAt (𝓡 n) (𝓘(ℝ, E →L[ℝ] ℝ)) P (e.symm (e q)) := by
      rwa [e.left_inv hq]
    have h := mvfderiv_chartVectorField_normed p P (e q) u (e.map_source hq) hPd'
    rw [e.left_inv hq] at h
    have hgerm : (fun y ↦ P (e.symm y)) =ᶠ[𝓝 (e q)] fderiv ℝ φ := by
      filter_upwards [e.open_target.mem_nhds (e.map_source hq)] with y hy
      exact congrArg (fderiv ℝ φ) (e.right_inv hy)
    exact h.trans (congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ ↦ L u)
      (hgerm.fderiv_eq (𝕜 := ℝ)))
  change mvfderiv (𝓡 n)
      (fun x ↦ mvfderiv (𝓡 n) f x (FiberBundle.extend E Vq x)) q
      (FiberBundle.extend E X q) -
      mvfderiv (𝓡 n) f q (D.connection (FiberBundle.extend E Vq)
        q (FiberBundle.extend E X q)) = _
  rw [FiberBundle.extend_apply_self, hder,
    connection_frozenChartCoordinates D p q hq X A hA v, hfirst q hqU, map_add, hPder]
  ring

end PoincareConjecture.Proofs.M09

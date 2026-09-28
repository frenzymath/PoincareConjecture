import PoincareConjecture.Proofs.M09.FixedChartTensor








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

theorem mvfderiv_chartVectorField_normed
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : M) (f : M → V) (y u : E) (hy : y ∈ (chartAt E p).target)
    (hf : MDifferentiableAt (𝓡 n) (𝓘(ℝ, V)) f ((chartAt E p).symm y)) :
    mvfderiv (𝓡 n) f ((chartAt E p).symm y)
        (chartVectorField p u ((chartAt E p).symm y)) =
      fderiv ℝ (fun z ↦ f ((chartAt E p).symm z)) y u := by
  rw [chartVectorField_at_inverse p u y hy]
  have h := mfderiv_comp y hf
    ((mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt_symm hy)
  rw [mfderiv_eq_fderiv] at h
  exact (congrArg (fun L ↦ L u) h).symm

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in
theorem hessian_fixedChart {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (f : M → ℝ) (p q : M) (hq : q ∈ (chartAt E p).source)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (chartAt E p).source)
    (u v : E) (A : E →L[ℝ] E)
    (hA : ∀ w : E, D.connection (chartVectorField p w) q (chartVectorField p u q) =
      chartVectorField p (A w) q) :
    let φ : E → ℝ := fun y ↦ f ((chartAt E p).symm y)
    D.hessian f q (chartVectorField p u q) (chartVectorField p v q) =
      fderiv ℝ (fderiv ℝ φ) ((chartAt E p) q) u v -
        fderiv ℝ φ ((chartAt E p) q) (A v) := by
  dsimp only
  let e := chartAt E p
  let φ : E → ℝ := fun y ↦ f (e.symm y)
  let P : M → E →L[ℝ] ℝ := fun x ↦ fderiv ℝ φ (e x)
  let X := chartVectorField p u q
  let V := chartVectorField p v q
  let c := frozenChartCoordinates p q V
  have hφ : ContDiffOn ℝ ∞ φ e.target :=
    (hf.comp contMDiffOn_chart_symm (fun y hy ↦ e.map_target hy)).contDiffOn
  have hDφ := hφ.fderiv_of_isOpen e.open_target (m := ∞) (by simp)
  have hP : ContMDiffOn (𝓡 n) (𝓘(ℝ, E →L[ℝ] ℝ)) ∞ P e.source :=
    hDφ.contMDiffOn.comp contMDiffOn_chart (fun x hx ↦ e.map_source hx)
  have hPd := (hP.contMDiffAt (e.open_source.mem_nhds hq)).mdifferentiableAt (by simp)
  have hcd := (frozenChartCoordinates_contMDiffAt p q hq V).mdifferentiableAt (by simp)
  have hcv : c q = v := frozenChartCoordinates_at_base p q hq v
  have hfirst (x : M) (hx : x ∈ e.source) (w : E) :
      mvfderiv (𝓡 n) f x (chartVectorField p w x) = P x w := by
    have hfx : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f (e.symm (e x)) := by
      rw [e.left_inv hx]
      exact (hf.contMDiffAt (e.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
    have h := mvfderiv_chartVectorField_normed p f (e x) w (e.map_source hx) hfx
    rwa [e.left_inv hx] at h
  have heq : (fun x ↦ mvfderiv (𝓡 n) f x (FiberBundle.extend E V x)) =ᶠ[𝓝 q]
      (fun x ↦ P x (c x)) := by
    filter_upwards [e.open_source.mem_nhds hq] with x hx
    rw [← frozenChartCoordinates_reconstruct p q x V hx]
    exact hfirst x hx (c x)
  have hder : mvfderiv (𝓡 n)
      (fun x ↦ mvfderiv (𝓡 n) f x (FiberBundle.extend E V x)) q X =
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
      (fun x ↦ mvfderiv (𝓡 n) f x (FiberBundle.extend E V x)) q
      (FiberBundle.extend E X q) -
      mvfderiv (𝓡 n) f q (D.connection (FiberBundle.extend E V)
        q (FiberBundle.extend E X q)) = _
  rw [FiberBundle.extend_apply_self, hder,
    connection_frozenChartCoordinates D p q hq X A hA v, hfirst q hq, map_add, hPder]
  ring

end PoincareConjecture.Proofs.M09

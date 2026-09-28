import PoincareConjecture.Proofs.M10.MinimizingLifts

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {C : Type u} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {J : Set ℝ} {F : RicciFlow n C J} {T τmax τ : ℝ} {p q : C}

theorem ordinaryCapture_harnackDensity_congr {γ δ : ℝ → C} {s : ℝ}
    (h : γ =ᶠ[𝓝 s] δ) (d : ℝ → ℝ) :
    reducedHarnackDensity F T γ d s = reducedHarnackDensity F T δ d s := by
  have hd := h.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  have hv : (curveVelocity (n := n) γ s : EuclideanSpace ℝ (Fin n)) =
      curveVelocity (n := n) δ s :=
    congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hd
  have hphase : (⟨γ s, curveVelocity (n := n) γ s⟩ : TangentBundle (𝓡 n) C) =
      ⟨δ s, curveVelocity (n := n) δ s⟩ :=
    Bundle.TotalSpace.ext h.eq_of_nhds (heq_of_eq hv)
  have hvalue := congrArg (fun v : TangentBundle (𝓡 n) C =>
    -d s - (F.connection (T - s)).scalarCurvature v.1 / s -
      2 * mvfderiv (𝓡 n) (F.connection (T - s)).scalarCurvature v.1 v.2 +
      2 * (F.connection (T - s)).ricci v.1 v.2 v.2) hphase
  unfold reducedHarnackDensity
  exact hvalue

noncomputable def ordinaryCaptureReplaceRegularPath
    (r : ReducedLengthRegularPoint F T τmax p q τ) (a : BackwardTimePath F T 0 τ)
    (heq : EqOn r.path.curve a.curve (Icc 0 τ)) :
    ReducedLengthRegularPoint F T τmax p q τ where
  tau_pos := r.tau_pos
  tau_lt := r.tau_lt
  path := a
  path_start := (heq ⟨le_rfl, r.tau_pos.le⟩).symm.trans r.path_start
  path_end := (heq ⟨r.tau_pos.le, le_rfl⟩).symm.trans r.path_end
  minimizing := M10.minimizing_of_eqOn r.minimizing heq
  path_realizes_reduced_length := r.path_realizes_reduced_length.trans
    (congrArg (fun b : ℝ => b / (2 * Real.sqrt τ))
      (M10.backwardLLength_eq_of_eqOn r.tau_pos.le heq))
  unique_minimizing_path := fun a' ha' hb' hm' =>
    (r.unique_minimizing_path a' ha' hb' hm').trans heq
  neighborhood := r.neighborhood
  neighborhood_open := r.neighborhood_open
  center_mem := r.center_mem
  representative := r.representative
  representative_eq := r.representative_eq
  representative_spacetime_smooth := r.representative_spacetime_smooth
  representative_space_smooth_on := r.representative_space_smooth_on
  representative_space_smooth := r.representative_space_smooth
  representative_time_derivative := r.representative_time_derivative
  path_scalar_time_derivative := r.path_scalar_time_derivative
  path_scalar_time_derivative_spec := by
    intro s hs
    simpa only [heq (Ioo_subset_Icc_self hs)] using r.path_scalar_time_derivative_spec s hs
  harnack_integrable := r.harnack_integrable.congr_uIoo (by
    intro s hs
    have hso : s ∈ Ioo 0 τ := by simpa only [uIoo_of_le r.tau_pos.le] using hs
    have hnear : r.path.curve =ᶠ[𝓝 s] a.curve :=
      eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hso) (heq.mono Ioo_subset_Icc_self)
    exact congrArg (fun b : ℝ => s * Real.sqrt s * b)
      (ordinaryCapture_harnackDensity_congr hnear r.path_scalar_time_derivative))

theorem ordinaryCaptureReplaceRegularPath_curve
    (r : ReducedLengthRegularPoint F T τmax p q τ) (a : BackwardTimePath F T 0 τ)
    (heq : EqOn r.path.curve a.curve (Icc 0 τ)) :
    (ordinaryCaptureReplaceRegularPath r a heq).path.curve = a.curve := rfl

end PoincareConjecture.M14

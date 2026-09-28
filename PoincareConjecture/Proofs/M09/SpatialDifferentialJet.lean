import PoincareConjecture.Proofs.M09.SpatialPartial








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem fderiv_initialSlice (f : E × ℝ → V) (x : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x, t)) :
    fderiv ℝ (fun y ↦ f (y, t)) x =
      (fderiv ℝ f (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ) := by
  have h := hf.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const t x))
  convert h.fderiv using 1 <;> ext W <;> rfl

theorem contDiffOn_initialSlice_fderiv (f : E × ℝ → V) (U : Set (E × ℝ))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ fderiv ℝ (fun y ↦ f (y, z.2)) z.1) U := by
  have hD := (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inl ℝ E ℝ))
  apply hD.congr
  intro z hz
  exact fderiv_initialSlice f z.1 z.2
    ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))

theorem contDiffOn_timeSlice_deriv (f : E × ℝ → V) (U : Set (E × ℝ))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun z : E × ℝ ↦ deriv (fun t ↦ f (z.1, t)) z.2) U := by
  have hD := (hf.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := ((0, 1) : E × ℝ)))
  apply hD.congr
  intro z hz
  exact (((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    z.2 ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv

theorem initialSlice_fderiv_zero (f : E × ℝ → V) (q : V)
    (hzero : ∀ x, f (x, 0) = q) (x : E) :
    fderiv ℝ (fun y ↦ f (y, 0)) x = 0 := by
  have heq : (fun y ↦ f (y, 0)) = fun _ ↦ q := funext hzero
  rw [heq]
  exact (hasFDerivAt_const (𝕜 := ℝ) q x).fderiv

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_initialSlice_fderiv_zero (f : E × ℝ → V) (U : Set (E × ℝ))
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hzero : ∀ x, (x, (0 : ℝ)) ∈ U) (L : E →L[ℝ] V)
    (hjet : ∀ x, HasDerivAt (fun t ↦ f (x, t)) (L x) 0) (x : E) :
    HasDerivAt (fun t ↦ fderiv ℝ (fun y ↦ f (y, t)) x) L 0 := by
  let B : E × ℝ → E →L[ℝ] V := fun z ↦ fderiv ℝ (fun y ↦ f (y, z.2)) z.1
  let G : ℝ × E → V := fun z ↦ f (z.2, z.1)
  have hB := contDiffOn_initialSlice_fderiv f U hU hf
  have hBa := hB.contDiffAt (hU.mem_nhds (hzero x))
  have hBt : DifferentiableAt ℝ (fun t ↦ B (x, t)) 0 :=
    (hBa.comp 0 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  have hGa (y : E) : ContDiffAt ℝ ∞ G (0, y) :=
    (hf.contDiffAt (hU.mem_nhds (hzero y))).comp (0, y)
      (contDiffAt_snd.prodMk contDiffAt_fst)
  have hVeq : (fun y ↦ fderiv ℝ G (0, y) (1, 0)) = fun y ↦ L y := by
    funext y
    have hd : HasDerivAt (fun t ↦ G (t, y)) (fderiv ℝ G (0, y) (1, 0)) 0 := by
      simpa only [Function.comp_def, id_eq] using
        ((hGa y).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
          0 ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 y))
    exact hd.unique (hjet y)
  have hresult : deriv (fun t ↦ B (x, t)) 0 = L := by
    ext W
    have htime := hasDerivAt_spatialDerivative_time G 0 x W (hGa x)
    rw [hVeq, L.fderiv] at htime
    have hagree : (fun t ↦ B (x, t) W) =ᶠ[𝓝 (0 : ℝ)]
        (fun t ↦ fderiv ℝ G (t, x) (0, W)) := by
      filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (hU.mem_nhds (hzero x))] with t ht
      have hGt : DifferentiableAt ℝ G (t, x) :=
        ((hf.contDiffAt (hU.mem_nhds ht)).comp (t, x)
          (contDiffAt_snd.prodMk contDiffAt_fst)).differentiableAt (by simp)
      change fderiv ℝ (fun y ↦ G (t, y)) x W = _
      rw [fderiv_spatialSlice G t x hGt]
      rfl
    have hactual := htime.congr_of_eventuallyEq hagree
    have hvalue := hBt.hasDerivAt.clm_apply (hasDerivAt_const 0 W)
    simpa only [map_zero, add_zero] using hvalue.unique hactual
  exact hBt.hasDerivAt.congr_deriv hresult

end PoincareConjecture.Proofs.M09

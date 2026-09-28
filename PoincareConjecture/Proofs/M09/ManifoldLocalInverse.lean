import PoincareConjecture.Proofs.M09.LocalSmoothInverse
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff

namespace PoincareConjecture.Proofs.M09

variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold (𝓘(ℝ, F)) ∞ N]

set_option backward.isDefEq.respectTransparency false in
theorem exists_manifold_local_inverse (f : E → N) (S : Set E) (hS : IsOpen S)
    (hf : ContMDiffOn (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ f S) (x : E) (hx : x ∈ S)
    (hbij : Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x)) :
    ∃ e : OpenPartialHomeomorph E N, x ∈ e.source ∧ e.source ⊆ S ∧
      Set.EqOn (e : E → N) f e.source ∧
      ContMDiffOn (𝓘(ℝ, F)) (𝓘(ℝ, E)) ∞ e.symm e.target ∧
      ∀ y ∈ e.source, Function.Bijective (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f y) := by
  let c := chartAt F (f x)
  let D := S ∩ f ⁻¹' c.source
  let g : E → F := fun y ↦ c (f y)
  have hD : IsOpen D := hf.continuousOn.isOpen_inter_preimage hS c.open_source
  have hxD : x ∈ D := ⟨hx, mem_chart_source F (f x)⟩
  have hg : ContDiffOn ℝ ∞ g D :=
    (contMDiffOn_chart.comp (hf.mono Set.inter_subset_left) (fun y hy ↦ hy.2)).contDiffOn
  have hchain (y : E) (hy : y ∈ D) : fderiv ℝ g y =
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) c (f y)).comp
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f y) := by
    have hc := (mdifferentiable_chart (I := 𝓘(ℝ, F)) (f x)).mdifferentiableAt hy.2
    have hfy := (hf.contMDiffAt (hS.mem_nhds hy.1)).mdifferentiableAt (by simp)
    have hcomp : HasFDerivAt g
        ((mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) c (f y)).comp
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f y)) y :=
      (hc.hasMFDerivAt.comp y hfy.hasMFDerivAt).hasFDerivAt
    exact hcomp.fderiv
  have hchart (y : E) (hy : y ∈ D) :
      Function.Bijective (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) c (f y)) :=
    (mdifferentiable_chart (I := 𝓘(ℝ, F)) (f x)).mfderiv_bijective hy.2
  have hgx : Function.Bijective (fderiv ℝ g x) := by
    rw [hchain x hxD]
    exact (hchart x hxD).comp hbij
  obtain ⟨e0, hx0, h0D, he0, hinv, hderiv⟩ := exists_smooth_local_inverse g D hD hg x hxD hgx
  let e := e0.trans c.symm
  have hxsrc : x ∈ e.source := by
    refine ⟨hx0, ?_⟩
    change e0 x ∈ c.target
    rw [he0]
    exact c.map_source hxD.2
  have hsrcD : e.source ⊆ D := fun y hy ↦ h0D hy.1
  refine ⟨e, hxsrc, (fun y hy ↦ (hsrcD hy).1), ?_, ?_, ?_⟩
  · intro y hy
    change c.symm (e0 y) = f y
    rw [he0]
    exact c.left_inv (hsrcD hy).2
  · have hc : ContMDiffOn (𝓘(ℝ, F)) (𝓘(ℝ, F)) ∞ c e.target :=
      contMDiffOn_chart.mono (fun y hy ↦ hy.1)
    exact hinv.contMDiffOn.comp hc (fun y hy ↦ hy.2)
  · intro y hy
    have hb := hderiv y hy.1
    rw [hchain y (hsrcD hy)] at hb
    constructor
    · intro v w hvw
      apply hb.1
      exact congrArg (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) c (f y)) hvw
    · intro v
      obtain ⟨w, hw⟩ := hb.2 (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) c (f y) v)
      exact ⟨w, (hchart y (hsrcD hy)).1 hw⟩

end PoincareConjecture.Proofs.M09

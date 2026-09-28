import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.Pullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace PoincareConjecture.M60

universe u

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold (𝓡 2) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_local_smooth_inverse_surface
    (f : Plane → M) {S : Set Plane} (hS : IsOpen S)
    (hf : ContMDiffOn (𝓡 2) (𝓡 2) ∞ f S)
    (hinv : ∀ y ∈ S, (mfderiv (𝓡 2) (𝓡 2) f y).IsInvertible)
    {x : Plane} (hx : x ∈ S) :
    ∃ e : OpenPartialHomeomorph Plane M,
      x ∈ e.source ∧ e.source ⊆ S ∧ EqOn e f e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target := by
  let c := extChartAt (𝓡 2) (f x)
  let F : Plane → Plane := c ∘ f
  have hfc : ContMDiffAt (𝓡 2) (𝓡 2) ∞ f x := hf.contMDiffAt (hS.mem_nhds hx)
  have hcx : f x ∈ c.source := mem_extChartAt_source (f x)
  have hcopen : IsOpen c.source := isOpen_extChartAt_source (f x)
  have hnhds : S ∩ f ⁻¹' c.source ∈ 𝓝 x := inter_mem (hS.mem_nhds hx)
    (hfc.continuousAt.preimage_mem_nhds (hcopen.mem_nhds hcx))
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hnhds
  have hF (y : Plane) (hy : y ∈ U) : ContDiffAt ℝ ∞ F y := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffOn_extChartAt (I := 𝓡 2) (x := f x)).contMDiffAt
      (by simpa only [c, extChartAt_source] using hcopen.mem_nhds (hUsub hy).2) |>.comp y
        (hf.contMDiffAt (hS.mem_nhds (hUsub hy).1))
  have hFi (y : Plane) (hy : y ∈ U) : (fderiv ℝ F y).IsInvertible := by
    have hcf := ((contMDiffOn_extChartAt (I := 𝓡 2) (n := ∞) (x := f x)).contMDiffAt
      (by simpa only [c, extChartAt_source] using hcopen.mem_nhds (hUsub hy).2)).mdifferentiableAt
        (by simp)
    have hfy := (hf.contMDiffAt (hS.mem_nhds (hUsub hy).1)).mdifferentiableAt (by simp)
    rw [← mfderiv_eq_fderiv]
    change (mfderiv (𝓡 2) (𝓡 2) (c ∘ f) y).IsInvertible
    rw [mfderiv_comp y hcf hfy]
    exact (isInvertible_mfderiv_extChartAt (I := 𝓡 2) (hUsub hy).2).comp
      (hinv y (hUsub hy).1)
  obtain ⟨L, hL⟩ := hFi x hxU
  have hd : HasFDerivAt F (L : Plane →L[ℝ] Plane) x := by
    rw [hL]
    exact (hF x hxU).differentiableAt (by simp) |>.hasFDerivAt
  let e0 := (hF x hxU).toOpenPartialHomeomorph F hd (by simp)
  let e1 := e0.restr U
  have he1F : (e1 : Plane → Plane) = F := rfl
  have hsource1 : e1.source = e0.source ∩ U := e0.restr_source' U hU
  have hsourceU : e1.source ⊆ U := by rw [hsource1]; exact inter_subset_right
  have ht : e1.target ⊆ c.target := by
    intro y hy
    have hy' := c.map_source (hUsub (hsourceU (e1.map_target hy))).2
    change F (e1.symm y) ∈ c.target at hy'
    rw [← he1F, e1.right_inv hy] at hy'
    exact hy'
  have he1smooth : ContDiffOn ℝ ∞ e1 e1.source := by
    rw [he1F]
    exact fun y hy => (hF y (hsourceU hy)).contDiffWithinAt
  have he1inv : ContDiffOn ℝ ∞ e1.symm e1.target := by
    intro y hy
    have hu := hsourceU (e1.map_target hy)
    obtain ⟨Ly, hLy⟩ := hFi _ hu
    apply ContDiffAt.contDiffWithinAt
    apply e1.contDiffAt_symm (f₀' := Ly) hy
    · rw [he1F, hLy]
      exact (hF _ hu).differentiableAt (by simp) |>.hasFDerivAt
    · rw [he1F]
      exact hF _ hu
  let e : OpenPartialHomeomorph Plane M := e1.trans (chartAt Plane (f x)).symm
  have hsource : e.source = e1.source := by
    ext y
    constructor
    · exact fun hy => hy.1
    · intro hy
      refine ⟨hy, ?_⟩
      simpa [c, extChartAt_target] using ht (e1.map_source hy)
  have heq : EqOn e f e.source := by
    intro y hy
    change c.symm (F y) = f y
    exact c.left_inv (hUsub (hsourceU (hsource ▸ hy))).2
  refine ⟨e, ?_, ?_, heq, ?_, ?_⟩
  · rw [hsource, hsource1]
    exact ⟨(hF x hxU).mem_toOpenPartialHomeomorph_source hd (by simp), hxU⟩
  · rw [hsource]
    exact hsourceU.trans (fun _ hy => (hUsub hy).1)
  · change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (c.symm ∘ e1) e.source
    rw [hsource]
    exact (contMDiffOn_extChartAt_symm (I := 𝓡 2) (f x)).comp
      (contMDiffOn_iff_contDiffOn.mpr he1smooth) (fun y hy => ht (e1.map_source hy))
  · change ContMDiffOn (𝓡 2) (𝓡 2) ∞ (e1.symm ∘ c) e.target
    apply (contMDiffOn_iff_contDiffOn.mpr he1inv).comp
      ((contMDiffOn_extChartAt (I := 𝓡 2) (x := f x)).mono (fun _ hy => hy.1))
    exact fun _ hy => hy.2

end PoincareConjecture.M60

end

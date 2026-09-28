import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M10

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def timeSliceHomeomorph (e : OpenPartialHomeomorph (X × ℝ) (Y × ℝ))
    (htime : ∀ z, (e z).2 = z.2)
    (hitime : ∀ z ∈ e.target, (e.symm z).2 = z.2) (t : ℝ) :
    OpenPartialHomeomorph X Y where
  toFun := fun x ↦ (e (x, t)).1
  invFun := fun y ↦ (e.symm (y, t)).1
  source := {x | (x, t) ∈ e.source}
  target := {y | (y, t) ∈ e.target}
  map_source' := by
    intro x hx
    have h := e.map_source hx
    have heq : e (x, t) = ((e (x, t)).1, t) := Prod.ext rfl (htime (x, t))
    rwa [heq] at h
  map_target' := by
    intro y hy
    have h := e.map_target hy
    have heq : e.symm (y, t) = ((e.symm (y, t)).1, t) :=
      Prod.ext rfl (hitime (y, t) hy)
    rwa [heq] at h
  left_inv' := by
    intro x hx
    have heq : e (x, t) = ((e (x, t)).1, t) := Prod.ext rfl (htime (x, t))
    change (e.symm ((e (x, t)).1, t)).1 = x
    rw [← heq]
    exact congrArg Prod.fst (e.left_inv hx)
  right_inv' := by
    intro y hy
    have heq : e.symm (y, t) = ((e.symm (y, t)).1, t) :=
      Prod.ext rfl (hitime (y, t) hy)
    change (e ((e.symm (y, t)).1, t)).1 = y
    rw [← heq]
    exact congrArg Prod.fst (e.right_inv hy)
  open_source := e.open_source.preimage (continuous_id.prodMk continuous_const)
  open_target := e.open_target.preimage (continuous_id.prodMk continuous_const)
  continuousOn_toFun :=
    (e.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hx ↦ hx)).fst
  continuousOn_invFun :=
    (e.symm.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hy ↦ hy)).fst

end Topology

section Smoothness

variable {n : ℕ} {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem timeSliceHomeomorph_contMDiffOn
    (e : OpenPartialHomeomorph (E × ℝ) (M × ℝ))
    (htime : ∀ z, (e z).2 = z.2)
    (hitime : ∀ z ∈ e.target, (e.symm z).2 = z.2) (t : ℝ)
    {k : ℕ∞ω}
    (he : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ)))
      ((𝓡 n).prod (𝓘(ℝ, ℝ))) k e e.source) :
    ContMDiffOn 𝓘(ℝ, E) (𝓡 n) k (timeSliceHomeomorph e htime hitime t)
      (timeSliceHomeomorph e htime hitime t).source :=
  contMDiff_fst.comp_contMDiffOn
    (he.comp (contMDiff_id.prodMk (contMDiff_const (c := t))).contMDiffOn (fun _ hx ↦ hx))

theorem timeSliceHomeomorph_symm_contMDiffOn
    (e : OpenPartialHomeomorph (E × ℝ) (M × ℝ))
    (htime : ∀ z, (e z).2 = z.2)
    (hitime : ∀ z ∈ e.target, (e.symm z).2 = z.2) (t : ℝ)
    {k : ℕ∞ω}
    (he : ContMDiffOn ((𝓡 n).prod (𝓘(ℝ, ℝ)))
      ((𝓘(ℝ, E)).prod (𝓘(ℝ, ℝ))) k e.symm e.target) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, E) k (timeSliceHomeomorph e htime hitime t).symm
      (timeSliceHomeomorph e htime hitime t).target :=
  contMDiff_fst.comp_contMDiffOn
    (he.comp (contMDiff_id.prodMk (contMDiff_const (c := t))).contMDiffOn (fun _ hx ↦ hx))

end Smoothness

end PoincareConjecture.M10

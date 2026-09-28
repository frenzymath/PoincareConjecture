import Mathlib.Geometry.Manifold.ContMDiff.Basic










set_option autoImplicit false

open scoped Manifold ContDiff Topology

noncomputable section

namespace PoincareConjecture.Proofs.M59

variable {E H X F K M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace K M]



def openMapExtension (U : TopologicalSpace.Opens X) (g : U → M) (p : M) (x : X) : M := by
  classical
  exact if hx : x ∈ U then g ⟨x, hx⟩ else p

omit [TopologicalSpace M] in


theorem openMapExtension_apply (U : TopologicalSpace.Opens X) (g : U → M) (p : M) (x : U) :
    openMapExtension U g p x.val = g x := by
  simp only [openMapExtension, dif_pos x.property]



theorem contMDiffAt_openMapExtension (U : TopologicalSpace.Opens X) (g : U → M) (p : M)
    (x : U) {n : ℕ∞ω} (hg : ContMDiffAt I J n g x) :
    ContMDiffAt I J n (openMapExtension U g p) x.val := by
  apply (contMDiffAt_subtype_iff (U := U) (x := x)).mp
  have heq : (fun y : U => openMapExtension U g p y.val) = g :=
    funext (openMapExtension_apply U g p)
  rw [heq]
  exact hg

end PoincareConjecture.Proofs.M59

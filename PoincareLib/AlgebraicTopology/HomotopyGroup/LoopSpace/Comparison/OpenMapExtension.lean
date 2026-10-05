import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Totalizing a map defined on an open submanifold

Values outside the open domain are irrelevant to local smoothness inside it.
This elementary adapter lets the punctured-plane approximation supply the
total extension field of a C1 loop. Source: the approximation derivation
for MT Claim 18.16, printed p. 430.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

noncomputable section

namespace PoincareMT.Proofs.M59

variable {E H X F K M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [TopologicalSpace X] [ChartedSpace H X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace K M]

/-- Extend a map by a chosen value outside its open domain.
Source: the total-loop-extension convention of MT, pp. 429-430. -/
def openMapExtension (U : TopologicalSpace.Opens X) (g : U → M) (p : M) (x : X) : M := by
  classical
  exact if hx : x ∈ U then g ⟨x, hx⟩ else p

omit [TopologicalSpace M] in
/-- On the open domain the totalization is the original map.
Source: MT Claim 18.16, p. 430, approximation derivation. -/
theorem openMapExtension_apply (U : TopologicalSpace.Opens X) (g : U → M) (p : M) (x : U) :
    openMapExtension U g p x.val = g x := by
  simp only [openMapExtension, dif_pos x.property]

/-- Totalization retains smoothness at every point of the open domain.
Source: MT Claim 18.16, p. 430, approximation derivation. -/
theorem contMDiffAt_openMapExtension (U : TopologicalSpace.Opens X) (g : U → M) (p : M)
    (x : U) {n : ℕ∞ω} (hg : ContMDiffAt I J n g x) :
    ContMDiffAt I J n (openMapExtension U g p) x.val := by
  apply (contMDiffAt_subtype_iff (U := U) (x := x)).mp
  have heq : (fun y : U => openMapExtension U g p y.val) = g :=
    funext (openMapExtension_apply U g p)
  rw [heq]
  exact hg

end PoincareMT.Proofs.M59

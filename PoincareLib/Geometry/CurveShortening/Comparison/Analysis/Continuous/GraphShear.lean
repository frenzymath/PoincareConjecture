import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Local shear coordinates of a continuous graph

Vertical translation straightens a continuous graph on an open domain.
This supports the topological side selection at the piecewise smooth
straight contact in MT Claim 19.40; no smoothness is imposed on the graph.
-/

set_option autoImplicit false

open Set

namespace PoincareMT

/-- The explicit shear over an open domain and its explicit inverse are continuous whenever
the graph function is continuous there. Source: MT Claim 19.40, pp. 470-471;
derivations/2026-09-27-minimal-contact-regularity.md, Section 9. -/
def m64ContinuousGraphShear
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [AddCommGroup F] [IsTopologicalAddGroup F]
    {h : E → F} {X : Set E} (hX : IsOpen X) (hh : ContinuousOn h X) :
    OpenPartialHomeomorph (E × F) (E × F) where
  toFun q := (q.1, h q.1 + q.2)
  invFun q := (q.1, q.2 - h q.1)
  source := X ×ˢ univ
  target := X ×ˢ univ
  map_source' _ hq := ⟨hq.1, mem_univ _⟩
  map_target' _ hq := ⟨hq.1, mem_univ _⟩
  left_inv' _ _ := by simp
  right_inv' _ _ := by simp
  open_source := hX.prod isOpen_univ
  open_target := hX.prod isOpen_univ
  continuousOn_toFun := continuousOn_fst.prodMk
    ((hh.comp continuousOn_fst (fun _ hq => hq.1)).add continuousOn_snd)
  continuousOn_invFun := continuousOn_fst.prodMk
    (continuousOn_snd.sub (hh.comp continuousOn_fst (fun _ hq => hq.1)))

end PoincareMT

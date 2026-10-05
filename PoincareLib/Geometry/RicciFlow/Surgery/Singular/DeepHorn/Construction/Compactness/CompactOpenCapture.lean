import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# A compact open set cannot be captured from a noncompact connected source

Morgan--Tian Claim 11.35, printed p. 290: a whole compact component
inside the actual convergence target would pull back to a compact open
nonempty subset of the connected noncompact limit. Reviewed derivation:
`claim11_35-closed-component-exclusion.md`, section 6.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M32

/-- A captured compact open nonempty set would make the entire source
compact. Source: Claim 11.35, printed p. 290; the ambient topological
argument is in `claim11_35-closed-component-exclusion.md`, section 6. -/
theorem compact_open_not_subset_partial_target
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [PreconnectedSpace X] (e : OpenPartialHomeomorph X Y)
    (hnoncompact : ¬ IsCompact (univ : Set X))
    {A : Set Y} (hcompact : IsCompact A) (hopen : IsOpen A) (hne : A.Nonempty) :
    ¬ A ⊆ e.target := by
  intro hA
  have hc : IsCompact (e.symm '' A) :=
    hcompact.image_of_continuousOn (e.continuousOn_symm.mono hA)
  have ho : IsOpen (e.symm '' A) := e.isOpen_image_symm_of_subset_target hopen hA
  have heq : e.symm '' A = univ := IsClopen.eq_univ ⟨hc.isClosed, ho⟩ (hne.image e.symm)
  exact hnoncompact (heq ▸ hc)

end PoincareMT.M32

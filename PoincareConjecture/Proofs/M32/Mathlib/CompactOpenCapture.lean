import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set

namespace PoincareConjecture.M32

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

end PoincareConjecture.M32

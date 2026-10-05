import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice

/-!
# Recovering the matching between copied and original rim arcs

Exact arc images and singleton fibers away from the marked endpoints force
the matching to be a permutation. No cyclic order or matching is supplied.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.OriginalTriangleCopies

theorem exists_rim_arc_matching
    {ι X Y : Type*} [Finite ι] (f : X → Y) (S : ι → Set X) (T : ι → Set Y)
    (marks : Set Y) (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (hnonempty : ∀ j, (T j \ marks).Nonempty)
    (hf : InjOn f ((⋃ i, S i) \ f ⁻¹' marks))
    (himage : ∀ i, ∃ j, f '' S i = T j) :
    ∃ e : ι ≃ ι, ∀ i, f '' S i = T (e i) := by
  classical
  choose a ha using himage
  have hinj : Function.Injective a := by
    intro i j hij
    by_contra hne
    obtain ⟨y, hy, hynot⟩ := hnonempty (a i)
    obtain ⟨x, hx, hfx⟩ := (ha i).symm.subset hy
    obtain ⟨z, hz, hfz⟩ := (ha j).symm.subset (hij ▸ hy)
    have hxz : x = z := hf
      ⟨mem_iUnion.mpr ⟨i, hx⟩, by simpa only [mem_preimage, hfx] using hynot⟩
      ⟨mem_iUnion.mpr ⟨j, hz⟩, by simpa only [mem_preimage, hfz] using hynot⟩
      (hfx.trans hfz.symm)
    exact disjoint_left.mp (hdis hne) hx (hxz.symm ▸ hz)
  exact ⟨Equiv.ofBijective a ⟨hinj, Finite.surjective_of_injective hinj⟩, ha⟩

end PoincareMT.M76.OriginalTriangleCopies

import Mathlib.Topology.Separation.Hausdorff









set_option autoImplicit false

open Set

namespace PoincareConjecture.M10

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]


theorem injective_of_open_dense_injOn {f : X → Y} (hf : Continuous f)
    (hfopen : IsOpenMap f) {S : Set X} (hS : IsOpen S) (hdense : Dense S)
    (hinj : InjOn f S) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  obtain ⟨U, V, hU, hV, hxU, hyV, hdisj⟩ := t2_separation hne
  have hopen₁ : IsOpen (U ∩ f ⁻¹' (f '' V)) := hU.inter ((hfopen V hV).preimage hf)
  have hnonempty₁ : (U ∩ f ⁻¹' (f '' V)).Nonempty :=
    ⟨x, hxU, y, hyV, hxy.symm⟩
  obtain ⟨u, huS, hu⟩ := hdense.exists_mem_open hopen₁ hnonempty₁
  obtain ⟨v, hvV, hvu⟩ := hu.2
  have hopen₂ : IsOpen (V ∩ f ⁻¹' (f '' (U ∩ S))) :=
    hV.inter ((hfopen (U ∩ S) (hU.inter hS)).preimage hf)
  have hnonempty₂ : (V ∩ f ⁻¹' (f '' (U ∩ S))).Nonempty :=
    ⟨v, hvV, u, ⟨hu.1, huS⟩, hvu.symm⟩
  obtain ⟨v', hv'S, hv'⟩ := hdense.exists_mem_open hopen₂ hnonempty₂
  obtain ⟨u', hu', heq⟩ := hv'.2
  have huv := hinj hu'.2 hv'S heq
  exact Set.disjoint_left.mp hdisj hu'.1 (huv.symm ▸ hv'.1)

end PoincareConjecture.M10

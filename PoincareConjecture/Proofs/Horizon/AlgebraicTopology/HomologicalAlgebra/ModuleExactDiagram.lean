import Mathlib.Algebra.Homology.ShortComplex.ModuleCat



set_option autoImplicit false

open CategoryTheory

universe u

namespace Poincare.Topology

theorem moduleExactDiagram_surjective
    {A B C D A' B' C' D' : ModuleCat.{u} Int}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (f' : A' ⟶ B') (g' : B' ⟶ C') (h' : C' ⟶ D')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g') (hh : h ≫ d = c ≫ h')
    (hgh : g' ≫ h' = 0)
    (hex : ∀ z : C, h z = 0 → ∃ y : B, g y = z)
    (hex' : ∀ y : B', g' y = 0 → ∃ x : A', f' x = y)
    (ha : Function.Surjective a) (hc : Function.Surjective c)
    (hd : Function.Injective d) : Function.Surjective b := by
  intro y
  obtain ⟨z, hz⟩ := hc (g' y)
  have hzero : h z = 0 := by
    apply hd
    rw [map_zero]
    change (h ≫ d) z = 0
    rw [hh]
    change h' (c z) = 0
    rw [hz]
    exact congrArg (fun k => k y) hgh
  obtain ⟨w, hw⟩ := hex z hzero
  have hy : g' (y - b w) = 0 := by
    have he := congrArg (fun k => k w) hg
    change c (g w) = g' (b w) at he
    rw [map_sub, ← he, hw, hz, sub_self]
  obtain ⟨x, hx⟩ := hex' (y - b w) hy
  obtain ⟨v, hv⟩ := ha x
  refine ⟨w + f v, ?_⟩
  have he := congrArg (fun k => k v) hf
  change b (f v) = f' (a v) at he
  rw [map_add, he, hv, hx]
  exact add_sub_cancel _ _

theorem moduleExactDiagram_injective
    {A B C D A' B' C' D' : ModuleCat.{u} Int}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (f' : A' ⟶ B') (g' : B' ⟶ C') (h' : C' ⟶ D')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hf : f ≫ b = a ≫ f') (hg : g ≫ c = b ≫ g') (hh : h ≫ d = c ≫ h')
    (hfg : f ≫ g = 0)
    (hex : ∀ z : C, h z = 0 → ∃ y : B, g y = z)
    (hex' : ∀ y : B', g' y = 0 → ∃ x : A', f' x = y)
    (ha : Function.Surjective a) (hb : Function.Injective b)
    (hd : Function.Injective d) : Function.Injective c := by
  suffices hz : ∀ z : C, c z = 0 → z = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, hxy, sub_self]
  intro z hz
  have hzero : h z = 0 := by
    apply hd
    rw [map_zero]
    change (h ≫ d) z = 0
    rw [hh]
    change h' (c z) = 0
    rw [hz, map_zero]
  obtain ⟨y, hy⟩ := hex z hzero
  have hzero' : g' (b y) = 0 := by
    change (b ≫ g') y = 0
    rw [← hg]
    change c (g y) = 0
    rw [hy, hz]
  obtain ⟨x, hx⟩ := hex' (b y) hzero'
  obtain ⟨w, hw⟩ := ha x
  have hy' : f w = y := by
    apply hb
    change (f ≫ b) w = b y
    rw [hf]
    change f' (a w) = b y
    rw [hw, hx]
  rw [← hy, ← hy']
  exact congrArg (fun k => k w) hfg

end Poincare.Topology

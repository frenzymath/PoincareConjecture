import PoincareConjecture.Proofs.M04.CompactDomainParabolic
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

theorem compact_subset_min_velocity_nonnegative_Icc
    {M : Type u} [TopologicalSpace M] {C : Set M} (hC : IsCompact C)
    {a b K : ℝ} (hab : a < b) (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ C))
    (hderiv : ∀ t ∈ Icc a b, ∀ x ∈ C,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc a b) t)
    (hmin : ∀ t ∈ Ioc a b, ∀ x ∈ C,
      (∀ y ∈ C, f t x ≤ f t y) → f t x < 0 → -K * f t x ≤ v t x)
    (hinit : ∀ x ∈ C, 0 ≤ f a x) :
    ∀ t ∈ Icc a b, ∀ x ∈ C, 0 ≤ f t x := by
  have hshift : MapsTo (fun s : ℝ ↦ a + s) (Icc 0 (b - a)) (Icc a b) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hc : ContinuousOn (fun p : ℝ × M ↦ f (a + p.1) p.2)
      (Icc 0 (b - a) ×ˢ C) :=
    hf.comp ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
      (fun p hp ↦ ⟨hshift hp.1, hp.2⟩)
  have hd : ∀ s ∈ Icc 0 (b - a), ∀ x ∈ C,
      HasDerivWithinAt (fun r ↦ f (a + r) x) (v (a + s) x) (Icc 0 (b - a)) s := by
    intro s hs x hx
    have ha : HasDerivWithinAt (fun r : ℝ ↦ a + r) 1 (Icc 0 (b - a)) s := by
      simpa only [id_eq] using ((hasDerivAt_id s).const_add a).hasDerivWithinAt
    simpa only [Function.comp_def, mul_one] using
      (hderiv (a + s) (hshift hs) x hx).comp s ha hshift
  have hm : ∀ s ∈ Ioc 0 (b - a), ∀ x ∈ C,
      (∀ y ∈ C, f (a + s) x ≤ f (a + s) y) → f (a + s) x < 0 →
        -K * f (a + s) x ≤ v (a + s) x := by
    intro s hs x hx hminx hneg
    apply hmin (a + s) (by constructor <;> linarith [hs.1, hs.2]) x hx hminx hneg
  have hi : ∀ x ∈ C, 0 ≤ f (a + 0) x := by simpa only [add_zero] using hinit
  have h := compact_subset_min_velocity_nonnegative hC (K := K) (sub_pos.mpr hab)
    (fun s x ↦ f (a + s) x) (fun s x ↦ v (a + s) x) hc hd hm hi
  intro t ht x hx
  have ht' : t - a ∈ Icc 0 (b - a) := by constructor <;> linarith [ht.1, ht.2]
  have he : a + (t - a) = t := by ring
  simpa only [he] using h (t - a) ht' x hx

theorem ricciFlow_compactDomain_supersolution_nonnegative_Icc
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} {a b K : ℝ} (hab : a < b) (F : RicciFlow n M J)
    (_hJ : Icc a b ⊆ J)
    {U C : Set M} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ C))
    (hderiv : ∀ t ∈ Icc a b, ∀ x ∈ C,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc a b) t)
    (hinit : ∀ x ∈ C, 0 ≤ f a x)
    (hsmooth : ∀ t ∈ Icc a b, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f t) U)
    (hboundary : ∀ t ∈ Icc a b, ∀ x ∈ C \ interior C, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioc a b, ∀ x ∈ interior C,
      (F.connection t).laplacian (f t) x - K * f t x ≤ v t x) :
    ∀ t ∈ Icc a b, ∀ x ∈ C, 0 ≤ f t x := by
  apply compact_subset_min_velocity_nonnegative_Icc hC (K := K) hab f v hf hderiv _ hinit
  intro t ht x hx hmin hneg
  have hxint : x ∈ interior C := by
    by_contra hn
    exact (not_lt_of_ge (hboundary t ⟨ht.1.le, ht.2⟩ x ⟨hx, hn⟩)) hneg
  have hlocal : IsLocalMin (f t) x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hxint] with y hy
    exact hmin y hy
  have hlap := (F.connection t).laplacian_nonneg_of_isLocalMin
    ((hsmooth t ⟨ht.1.le, ht.2⟩).contMDiffAt (hU.mem_nhds (hCU hx))) hlocal
  have hv := hevol t ht x hxint
  linarith

end PoincareConjecture.M04

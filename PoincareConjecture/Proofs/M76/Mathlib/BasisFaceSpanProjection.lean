import PoincareConjecture.Proofs.M76.Mathlib.BasisSecantCones

set_option autoImplicit false

open Set

namespace Module.Basis

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem secantCone_self_eq_span (b : Basis ι ℝ E) (s : Set ι) :
    b.secantCone s s = (Submodule.span ℝ (b '' s) : Set E) := by
  ext x
  constructor
  · intro hx
    apply b.mem_span_image.mpr
    intro i hi
    by_contra his
    exact Finsupp.mem_support_iff.mp hi (le_antisymm (hx.2 i his) (hx.1 i his))
  · intro hx
    have hs := b.mem_span_image.mp hx
    have hz : ∀ i ∉ s, b.repr x i = 0 := by
      intro i hi
      exact Finsupp.notMem_support_iff.mp (fun h => hi (hs h))
    exact ⟨fun i hi => (hz i hi).ge, fun i hi => (hz i hi).le⟩

theorem injOn_span_of_injOn_simplex [Finite ι] (b : Basis ι ℝ E) {s : Set ι}
    (Q : E →L[ℝ] F) (hQ : InjOn Q (convexHull ℝ (insert 0 (b '' s)))) :
    InjOn Q (Submodule.span ℝ (b '' s)) := by
  intro x hx y hy he
  apply sub_eq_zero.mp
  apply b.eq_zero_of_mem_secantCone_of_injOn (s := s) (t := s) Q
    (by simpa only [union_self] using hQ)
  · rw [b.secantCone_self_eq_span]
    exact (Submodule.span ℝ (b '' s)).sub_mem hx hy
  · rw [map_sub, he, sub_self]

theorem linearIndepOn_of_injOn_simplex [Finite ι] (b : Basis ι ℝ E) {s : Set ι}
    (Q : E →L[ℝ] F) (hQ : InjOn Q (convexHull ℝ (insert 0 (b '' s)))) :
    LinearIndepOn ℝ (fun i => Q (b i)) s :=
  (b.linearIndependent.linearIndepOn s).map_injOn Q.toLinearMap
    (b.injOn_span_of_injOn_simplex Q hQ)

end Module.Basis

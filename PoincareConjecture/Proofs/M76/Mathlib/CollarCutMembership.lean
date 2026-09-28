import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas











set_option autoImplicit false

open Set

namespace Set




theorem IsPreconnected.mem_closed_cut_iff {X : Type*} [TopologicalSpace X]
    {S s₀ s₁ : Set X} (hS : IsPreconnected S) (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁)
    (hcover : S ⊆ s₀ ∪ s₁) (hdisj : S ∩ (s₀ ∩ s₁) = ∅)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    (x ∈ s₀ ↔ y ∈ s₀) ∧ (x ∈ s₁ ↔ y ∈ s₁) := by
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS s₀ s₁ hs₀ hs₁ hcover hdisj
    with h | h
  · exact ⟨iff_of_true (h hx) (h hy), iff_of_false
      (fun hx₁ => (hdisj.subset ⟨hx, h hx, hx₁⟩).elim)
      (fun hy₁ => (hdisj.subset ⟨hy, h hy, hy₁⟩).elim)⟩
  · exact ⟨iff_of_false
      (fun hx₀ => (hdisj.subset ⟨hx, hx₀, h hx⟩).elim)
      (fun hy₀ => (hdisj.subset ⟨hy, hy₀, h hy⟩).elim), iff_of_true (h hx) (h hy)⟩

end Set

namespace Homeomorph

variable {E : Type*} [TopologicalSpace E]





theorem collar_fiber_mem_cut_iff
    {B T b s₀ s₁ : Set E} {upper A : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hs₀ : IsClosed s₀) (hs₁ : IsClosed s₁) (hcover : T ⊆ s₀ ∪ s₁)
    (hinter : s₀ ∩ s₁ ⊆ b) (hbzero : b ⊆ {x | A x = 0})
    (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)})
    (hbase : (p : E × ℝ).1 ∉ b) :
    ((C p : E) ∈ s₀ ↔ (p : E × ℝ).1 ∈ s₀) ∧
      ((C p : E) ∈ s₁ ↔ (p : E × ℝ).1 ∈ s₁) := by
  let x := (p : E × ℝ).1
  let I := Icc (0 : ℝ) (upper x)
  let P : I → {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} :=
    fun z => ⟨(x, z), p.property.1, z.property⟩
  let f : I → E := fun z => C (P z)
  have hP : Continuous P :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _
  have hf : Continuous f := continuous_subtype_val.comp (C.continuous.comp hP)
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hpre : IsPreconnected (range f) := isPreconnected_range hf
  have hcov : range f ⊆ s₀ ∪ s₁ := by
    rintro y ⟨z, rfl⟩
    exact hcover (C (P z)).property
  have hdisj : range f ∩ (s₀ ∩ s₁) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro y ⟨⟨z, rfl⟩, hy⟩
    have hfb : f z ∈ b := hinter hy
    have hz : (z : ℝ) = 0 := (hheight (P z)).symm.trans (hbzero hfb)
    exact hbase ((hbottom (P z) hz) ▸ hfb)
  have hmem : (C p : E) ∈ range f :=
    ⟨⟨(p : E × ℝ).2, p.property.2⟩, rfl⟩
  have hx : x ∈ range f := by
    let z : I := ⟨0, le_rfl, p.property.2.1.trans p.property.2.2⟩
    exact ⟨z, hbottom (P z) rfl⟩
  exact hpre.mem_closed_cut_iff hs₀ hs₁ hcov hdisj hmem hx

end Homeomorph

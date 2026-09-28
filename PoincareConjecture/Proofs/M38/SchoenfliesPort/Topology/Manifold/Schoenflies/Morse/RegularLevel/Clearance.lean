import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.RegularLevel.Tube
import Mathlib.Topology.MetricSpace.Thickening







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies










set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]



theorem exists_open_cylinder_avoiding_compact
    {D K : Set E} (hD : IsCompact D) (hK : IsCompact K) (hdisjoint : Disjoint D K)
    (v : E) (hv : ‖v‖ ≤ 1) :
    ∃ δ : Real, 0 < δ ∧ ∃ W : Set E, IsOpen W ∧ D ⊆ W ∧
      ∀ y ∈ W, ∀ t ∈ Icc (-δ) δ, y + t • v ∉ K := by
  obtain ⟨d, hd, hthick⟩ := hD.exists_thickening_subset_open hK.isClosed.isOpen_compl
    (fun y hy hyK => disjoint_left.mp hdisjoint hy hyK)
  refine ⟨d / 2, by positivity, thickening (d / 2) D, isOpen_thickening,
    self_subset_thickening (by positivity) D, ?_⟩
  intro y hy t ht
  apply hthick
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy
  refine mem_thickening_iff.mpr ⟨z, hz, ?_⟩
  have hnorm : ‖t • v‖ ≤ d / 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |t| * ‖v‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ ≤ d / 2 := by simpa only [mul_one] using abs_le.mpr ht
  have hdist : dist (y + t • v) y ≤ d / 2 := by
    simpa only [dist_eq_norm, add_sub_cancel_left] using hnorm
  exact (dist_triangle (y + t • v) y z).trans_lt (by linarith)



theorem exists_open_cylinder_clearance_of_compact_embedding
    {M : Type*} [TopologicalSpace M] [CompactSpace M]
    {f : M -> E} (hf : Continuous f) (hinj : Function.Injective f)
    {U : Set M} (hU : IsOpen U) {D : Set E} (hD : IsCompact D)
    (hintersection : D ∩ range f ⊆ f '' U) (v : E) (hv : ‖v‖ ≤ 1) :
    ∃ δ : Real, 0 < δ ∧ ∃ W : Set E, IsOpen W ∧ D ⊆ W ∧
      ∀ y ∈ W, ∀ t ∈ Icc (-δ) δ, ∀ x, f x = y + t • v -> x ∈ U := by
  have hK : IsCompact (f '' Uᶜ) := hU.isClosed_compl.isCompact.image hf
  have hdisjoint : Disjoint D (f '' Uᶜ) := by
    apply disjoint_left.mpr
    rintro y hy ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hzx⟩ := hintersection ⟨hy, mem_range_self x⟩
    exact hx (hinj hzx ▸ hz)
  obtain ⟨δ, hδ, W, hW, hDW, havoid⟩ :=
    exists_open_cylinder_avoiding_compact hD hK hdisjoint v hv
  refine ⟨δ, hδ, W, hW, hDW, ?_⟩
  intro y hy t ht x heq
  by_contra hx
  exact havoid y hy t ht ⟨x, hx, heq⟩

end Poincare.Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1
private abbrev S2 := sphere (0 : E3) 1





theorem exists_regular_tube_disk_clearance
    {f : S2 -> E3} (hf : Continuous f) (hinj : Function.Injective f)
    {v : E3} (hv : ‖v‖ = 1) {c ε r : Real} (hr : 0 < r) (hrε : r < ε)
    (F : OpenPartialHomeomorph (S1 × Real) S2)
    (hsource : F.source = univ ×ˢ Ioo (-ε) ε)
    {C : Set S2} (hcenter : range (fun q : S1 => F (q, 0)) = C)
    {D : Set E3} (hD : IsCompact D)
    (hplane : D ⊆ {y : E3 | inner Real v y = c})
    (hintersection : D ∩ range f = f '' C) :
    ∃ δ : Real, 0 < δ ∧ δ ≤ r ∧
      ∃ W : Set {y : E3 | inner Real v y = c},
        IsOpen W ∧ D ⊆ Subtype.val '' W ∧
        ((fun z : {y : E3 | inner Real v y = c} × Real => (z.1 : E3) + z.2 • v) ''
          (W ×ˢ Icc (-δ) δ)) ∩ range f ⊆
            f '' (F '' (univ ×ˢ Ioo (-r) r)) := by
  let U := F '' (univ ×ˢ Ioo (-r) r)
  have hU : IsOpen U := by
    apply F.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo)
    rw [hsource]
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hCU : C ⊆ U := by
    rw [← hcenter]
    rintro x ⟨q, rfl⟩
    exact ⟨(q, 0), ⟨mem_univ _, by constructor <;> linarith⟩, rfl⟩
  have hDU : D ∩ range f ⊆ f '' U := by
    rw [hintersection]
    exact image_mono hCU
  obtain ⟨d, hd, V, hV, hDV, hclear⟩ :=
    Poincare.Topology.exists_open_cylinder_clearance_of_compact_embedding
      hf hinj hU hD hDU v hv.le
  let W : Set {y : E3 | inner Real v y = c} := Subtype.val ⁻¹' V
  refine ⟨min d r, lt_min hd hr, min_le_right _ _, W,
    hV.preimage continuous_subtype_val, ?_, ?_⟩
  · intro y hy
    exact ⟨⟨y, hplane hy⟩, hDV hy, rfl⟩
  · rintro y ⟨⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩, ⟨x, hx⟩⟩
    refine ⟨x, hclear z hz t ?_ x hx, hx⟩
    exact ⟨(neg_le_neg (min_le_left d r)).trans ht.1,
      ht.2.trans (min_le_left d r)⟩

end Poincare.Manifold.Schoenflies

end M38Schoenflies

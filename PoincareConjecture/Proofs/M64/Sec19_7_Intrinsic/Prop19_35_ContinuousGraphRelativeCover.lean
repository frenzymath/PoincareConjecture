import PoincareConjecture.Proofs.M64.Mathlib.ContinuousGraphShear
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ProductLineRelativeCover









noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture




theorem m64Intrinsic_exists_continuous_graph_relative_cover
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    {h : ℝ → ℝ} {X : Set ℝ} (hX : IsOpen X) (hh : ContinuousOn h X)
    {p : AnnulusCoordinates} {U V W : Set AnnulusCoordinates}
    (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (hfV : frontier V = frontier U) (hW : IsOpen W) (hpW : p ∈ W)
    (hpfront : p ∈ frontier U)
    (hgraph : ∀ z ∈ W, (L z).1 ∈ X ∧ (z ∈ frontier U ↔ (L z).2 = h (L z).1))
    {K : Set AnnulusCoordinates} (hK : IsClosed K)
    (hKregular : closure (interior K) = K) (hKsub : K ⊆ closure U)
    (hpK : p ∈ K) {N : Set AnnulusCoordinates} (hN : N ∈ 𝓝 p)
    (hfrontK : N ∩ frontier K ⊆ frontier U) :
    ∃ O : Set AnnulusCoordinates, IsOpen O ∧ p ∈ O ∧ O ∩ closure U ⊆ K := by
  let H := (m64ContinuousGraphShear hX hh).trans L.symm.toHomeomorph.toOpenPartialHomeomorph
  have hsource : H.source = X ×ˢ univ := by
    ext q
    simp [H, m64ContinuousGraphShear]
  have hformula (q : ℝ × ℝ) : H q = L.symm (q.1, h q.1 + q.2) := rfl
  let x := (L p).1
  have hxX : x ∈ X := (hgraph p hpW).1
  have hpgraph : (L p).2 = h x := (hgraph p hpW).2.mp hpfront
  have hcoord : L p = (x, h x) := Prod.ext rfl hpgraph
  have hx : (x, (0 : ℝ)) ∈ H.source := by rw [hsource]; exact ⟨hxX, mem_univ _⟩
  have hbase : H (x, 0) = p := by rw [hformula, add_zero, ← hcoord, L.symm_apply_apply]
  have hpre : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ W :=
    (H.continuousAt hx).preimage_mem_nhds (by simpa only [hbase] using hW.mem_nhds hpW)
  have hline : ∀ᶠ z in 𝓝 (x, (0 : ℝ)), H z ∈ frontier U ↔ z.2 = 0 := by
    filter_upwards [hpre] with z hz
    rw [(hgraph (H z) hz).2, hformula, L.apply_symm_apply]
    simp only [add_eq_left]
  simpa only [hbase] using m64Intrinsic_exists_product_line_relative_cover hU hV hd
    hfV H hx (by simpa only [hbase] using hpfront) hline hK hKregular hKsub
    (by simpa only [hbase] using hpK) (by simpa only [hbase] using hN) hfrontK

end PoincareConjecture

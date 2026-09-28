import Mathlib.Geometry.Manifold.PartitionOfUnity
import PoincareConjecture.Proofs.M03.Existence.HalfSpaceExtensionNative










set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M63

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_finiteOrder_compact_extension (k : ℕ)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : E → F) (hf : ContDiffOn ℝ k f U) :
    ∃ g : C(E, F), ContDiff ℝ k g ∧ HasCompactSupport g ∧
      ∃ O : Set E, IsOpen O ∧ K ⊆ O ∧ O ⊆ U ∧ EqOn g f O := by
  obtain ⟨C, hC, hKC, hCU⟩ := exists_compact_between hK hU hKU
  have hd : Disjoint (interior C)ᶜ K := disjoint_left.mpr (fun x hx hxK => hx (hKC hxK))
  obtain ⟨eta, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
    isOpen_interior.isClosed_compl hK.isClosed hd (n := (⊤ : ℕ∞))
  have heta : ContDiff ℝ k (eta : E → ℝ) :=
    eta.contMDiff.contDiff.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)
  have hg : ContDiff ℝ k (fun x => eta x • f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact heta.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
    · have hxC : x ∈ (interior C)ᶜ := fun h => hx (hCU (interior_subset h))
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hxC)] with y hy
      simp only [hy, zero_smul]
  have hsupp : Function.support (fun x => eta x • f x) ⊆ C := by
    intro x hx
    by_contra hxC
    have hz : eta x = 0 := hzero.self_of_nhdsSet x (fun h => hxC (interior_subset h))
    exact hx (by simp only [hz, zero_smul])
  have hcompact : HasCompactSupport (fun x => eta x • f x) :=
    hC.of_isClosed_subset isClosed_closure (hC.isClosed.closure_subset_iff.mpr hsupp)
  obtain ⟨O, hO, hKO, hOone⟩ := mem_nhdsSet_iff_exists.mp hone
  refine ⟨⟨fun x => eta x • f x, hg.continuous⟩, hg, hcompact,
    O ∩ U, hO.inter hU, fun x hx => ⟨hKO hx, hKU hx⟩, inter_subset_right, ?_⟩
  intro x hx
  change eta x • f x = f x
  rw [hOone hx.1, one_smul]





theorem exists_finiteOrder_initialSlab_extension (k : ℕ)
    {U : Set E} (hU : IsOpen U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U)
    {T tau : ℝ} (hT : 0 < T) (_htau : 0 ≤ tau) (htauT : tau < T)
    (f : ℝ × E → F) (hf : ContDiffOn ℝ k f (Ico 0 T ×ˢ U)) :
    ∃ g : C(ℝ × E, F), ContDiff ℝ k g ∧ HasCompactSupport g ∧
      ∃ O : Set (ℝ × E), IsOpen O ∧ Icc 0 tau ×ˢ K ⊆ O ∧
        O ⊆ Iio T ×ˢ U ∧ EqOn g f (O ∩ (Ici 0 ×ˢ univ)) := by
  obtain ⟨c, hc⟩ := HalfSpaceExtensionNative.exists_reflectionWeights k
  let R := HalfSpaceExtensionNative.reflectionExtension c f
  let V : Set (ℝ × E) := Ioo (-T / ((k : ℝ) + 1)) T ×ˢ U
  have hV : IsOpen V := isOpen_Ioo.prod hU
  have hR : ContDiffOn ℝ k R V :=
    HalfSpaceExtensionNative.contDiffOn_reflectionExtension_slab_on k c hc f hT hU hf
  have hsub : Icc 0 tau ×ˢ K ⊆ V := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨(div_neg_of_neg_of_pos (neg_neg_of_pos hT) (by positivity)).trans_le ht.1,
      ht.2.trans_lt htauT⟩, hKU hx⟩
  obtain ⟨g, hg, hgc, O, hO, hKO, hOV, heq⟩ :=
    exists_finiteOrder_compact_extension k (isCompact_Icc.prod hK) hV hsub R hR
  refine ⟨g, hg, hgc, O, hO, hKO, fun z hz => ⟨(hOV hz).1.2, (hOV hz).2⟩, ?_⟩
  intro z hz
  exact (heq hz.1).trans (HalfSpaceExtensionNative.reflectionExtension_eqOn_upper c f hz.2)

end PoincareConjecture.M63

import PoincareConjecture.Proofs.M76.Mathlib.CompactAffineLeafChart
import PoincareConjecture.Proofs.M76.Mathlib.AffineLeafInverse
import PoincareConjecture.Proofs.M76.Mathlib.AffineLeafGerm
import Mathlib.Topology.NhdsSet

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_smooth_affineLeaf_extension_matching (a : F →ᴬ[ℝ] E)
    {Q : F → E →L[ℝ] F} (hQ : ContDiff ℝ ∞ Q)
    (hnorm : ∀ x, Function.RightInverse a.contLinear (Q x))
    {C S : Set F} (hC : IsCompact C) (hSC : S ⊆ C)
    {W : Set (E →L[ℝ] F)} (hW : IsOpen W) (hQW : MapsTo Q C W)
    {G : E → E →L[ℝ] F} {V : Set E} (hV : V ∈ 𝓝ˢ (a '' S))
    (hG : ContinuousOn G V)
    (hleaf : ∀ z ∈ V, ∀ᶠ w in 𝓝 z, w - z ∈ (G z).ker → G w = G z)
    (hslice : ∀ x ∈ S, (fun v => G (a v)) =ᶠ[𝓝 x] Q) :
    ∃ U : Set E, IsOpen U ∧ a '' C ⊆ U ∧
      ∃ g : E → E →L[ℝ] F, ContDiffOn ℝ ∞ g U ∧
        (∀ x ∈ C, ∀ᶠ v in 𝓝 x, g (a v) = Q v) ∧
        (∀ y ∈ U, Function.RightInverse a.contLinear (g y) ∧ g y ∈ W) ∧
        (∀ y ∈ U, ∀ᶠ w in 𝓝 y, w - y ∈ (g y).ker → g w = g y) ∧
        G =ᶠ[𝓝ˢ (a '' S)] g := by
  obtain ⟨e, he, hzero, hi⟩ := a.exists_smooth_affineLeaf_chart_of_compact hQ hnorm 0 hC
  let g : E → E →L[ℝ] F := fun y => Q (e.symm y).1
  have hg : ContDiffOn ℝ ∞ g e.target := hQ.comp_contDiffOn hi.fst
  have he0 (x : F) : e (x, 0) = a x := by rw [he, a.affineLeafMap_zero]
  have hbase (x : F) (hx : x ∈ C) : ∀ᶠ v in 𝓝 x, g (a v) = Q v := by
    have hn : ∀ᶠ v in 𝓝 x, (v, (0 : (Q 0).ker)) ∈ e.source :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (e.open_source.mem_nhds (hzero x hx))
    filter_upwards [hn] with v hv
    have h := e.left_inv hv
    rw [he0] at h
    change Q (e.symm (a v)).1 = Q v
    rw [h]
  let U := e.target ∩ g ⁻¹' W
  have hU : IsOpen U := hg.continuousOn.isOpen_inter_preimage e.open_target hW
  refine ⟨U, hU, ?_, g, hg.mono inter_subset_left, hbase, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← he0]
      exact e.map_source (hzero x hx)
    · change g (a x) ∈ W
      rw [(hbase x hx).self_of_nhds]
      exact hQW hx
  · exact fun y hy => ⟨hnorm (e.symm y).1, hy.2⟩
  · intro y hy
    filter_upwards [a.eventually_affineLeaf_base_eq Q 0 hnorm e he hy.1] with w hw hwy
    exact congrArg Q (hw hwy)
  · apply eventually_nhdsSet_iff_forall.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact a.eventuallyEq_affineLeaf_extension Q 0 hnorm e he (hzero x (hSC hx))
      (mem_nhdsSet_iff_forall.mp hV (a x) ⟨x, hx, rfl⟩) hG hleaf (hslice x hx)

end ContinuousAffineMap

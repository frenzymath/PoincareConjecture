import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set

theorem isConnected_between_continuous_graphs
    {K : Type*} [TopologicalSpace K] [ConnectedSpace K]
    {f g : K → ℝ} (hf : Continuous f) (hg : Continuous g) (hlt : ∀ q, f q < g q) :
    IsConnected {z : K × ℝ | f z.1 < z.2 ∧ z.2 < g z.1} := by
  let F : K × ℝ → K × ℝ := fun z => (z.1, f z.1 + z.2 * (g z.1 - f z.1))
  have hF : Continuous F :=
    continuous_fst.prodMk ((hf.comp continuous_fst).add
      (continuous_snd.mul ((hg.comp continuous_fst).sub (hf.comp continuous_fst))))
  have himage : F '' (univ ×ˢ Ioo (0 : ℝ) 1) =
      {z : K × ℝ | f z.1 < z.2 ∧ z.2 < g z.1} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      change f q < f q + t * (g q - f q) ∧ f q + t * (g q - f q) < g q
      have hwidth : 0 < g q - f q := sub_pos.mpr (hlt q)
      constructor
      · linarith [mul_pos ht.1 hwidth]
      · nlinarith [mul_pos (sub_pos.mpr ht.2) hwidth]
    · rintro ⟨q, s⟩ ⟨hlo, hhi⟩
      have hwidth : 0 < g q - f q := sub_pos.mpr (hlt q)
      refine ⟨(q, (s - f q) / (g q - f q)), ⟨mem_univ _, ?_⟩, ?_⟩
      · exact ⟨div_pos (sub_pos.mpr hlo) hwidth,
          (div_lt_one hwidth).mpr (by linarith)⟩
      · apply Prod.ext
        · rfl
        · change f q + (s - f q) / (g q - f q) * (g q - f q) = s
          rw [div_mul_cancel₀ _ hwidth.ne']
          ring
  rw [← himage]
  exact ((isConnected_univ : IsConnected (univ : Set K)).prod
    (isConnected_Ioo (show (0 : ℝ) < 1 by norm_num))).image F hF.continuousOn

namespace OpenPartialHomeomorph

theorem isConnected_compl_range_graph_of_fiberwise
    {K E B : Type*} [TopologicalSpace K] [ConnectedSpace K]
    [TopologicalSpace E] [TopologicalSpace B]
    (j : OpenPartialHomeomorph ℝ B) (T : OpenPartialHomeomorph (K × ℝ) E)
    (π : E → B) {a α β b : ℝ}
    (ha : a < α) (hαβ : α < β) (hb : β < b)
    (hj : j.source = Ioo a b) (hT : T.source = univ ×ˢ Ioo a b)
    (htarget : T.target = π ⁻¹' j.target)
    (hfiber : ∀ z ∈ T.source, π (T z) = j z.2)
    (hπ : Topology.IsCoinducing π)
    (hfibers : ∀ c : B, IsConnected (π ⁻¹' {c}))
    (hC : IsConnected ((j '' Ioo α β)ᶜ))
    (h : K → ℝ) (hh : Continuous h) (hrange : ∀ q, h q ∈ Ioo α β) :
    IsConnected ((range fun q => T (q, h q))ᶜ) := by
  have hjinner : Ioo α β ⊆ j.source := by
    rw [hj]
    exact fun _ hs => ⟨ha.trans hs.1, hs.2.trans hb⟩
  have hjα : α ∈ j.source := by rw [hj]; exact ⟨ha, hαβ.trans hb⟩
  have hjβ : β ∈ j.source := by rw [hj]; exact ⟨ha.trans hαβ, hb⟩
  have hαC : j α ∈ (j '' Ioo α β)ᶜ := by
    rintro ⟨s, hs, heq⟩
    exact (ne_of_gt hs.1) (j.injOn (hjinner hs) hjα heq)
  have hβC : j β ∈ (j '' Ioo α β)ᶜ := by
    rintro ⟨s, hs, heq⟩
    exact (ne_of_lt hs.2) (j.injOn (hjinner hs) hjβ heq)
  have hgraph (q : K) : (q, h q) ∈ T.source := by
    rw [hT]
    exact ⟨mem_univ _, ha.trans (hrange q).1, (hrange q).2.trans hb⟩
  let Dminus : Set (K × ℝ) := {z | a < z.2 ∧ z.2 < h z.1}
  let Dplus : Set (K × ℝ) := {z | h z.1 < z.2 ∧ z.2 < b}
  have hminusSub : Dminus ⊆ T.source := by
    intro z hz
    rw [hT]
    exact ⟨mem_univ _, hz.1, hz.2.trans ((hrange z.1).2.trans hb)⟩
  have hplusSub : Dplus ⊆ T.source := by
    intro z hz
    rw [hT]
    exact ⟨mem_univ _, (ha.trans (hrange z.1).1).trans hz.1, hz.2⟩
  have hminus : IsConnected (T '' Dminus) :=
    (isConnected_between_continuous_graphs continuous_const hh
      (fun q => ha.trans (hrange q).1)).image T (T.continuousOn.mono hminusSub)
  have hplus : IsConnected (T '' Dplus) :=
    (isConnected_between_continuous_graphs hh continuous_const
      (fun q => (hrange q).2.trans hb)).image T (T.continuousOn.mono hplusSub)
  have hclosed : IsClosed ((j '' Ioo α β)ᶜ) :=
    (j.isOpen_image_of_subset_source isOpen_Ioo hjinner).isClosed_compl
  have hzero : IsConnected (π ⁻¹' ((j '' Ioo α β)ᶜ)) :=
    Topology.IsCoinducing.isConnected_preimage_of_isClosed hfibers hπ hclosed hC
  obtain ⟨q₀⟩ := (inferInstance : Nonempty K)
  have hTα : (q₀, α) ∈ T.source := by
    rw [hT]
    exact ⟨mem_univ _, ha, hαβ.trans hb⟩
  have hTβ : (q₀, β) ∈ T.source := by
    rw [hT]
    exact ⟨mem_univ _, ha.trans hαβ, hb⟩
  have hmeetMinus : ((π ⁻¹' ((j '' Ioo α β)ᶜ)) ∩ T '' Dminus).Nonempty := by
    refine ⟨T (q₀, α), ?_, ⟨(q₀, α), ⟨ha, (hrange q₀).1⟩, rfl⟩⟩
    change π (T (q₀, α)) ∈ (j '' Ioo α β)ᶜ
    rw [hfiber _ hTα]
    exact hαC
  have hmeetPlus : (((π ⁻¹' ((j '' Ioo α β)ᶜ)) ∪ T '' Dminus) ∩
      T '' Dplus).Nonempty := by
    refine ⟨T (q₀, β), Or.inl ?_, ⟨(q₀, β), ⟨(hrange q₀).2, hb⟩, rfl⟩⟩
    change π (T (q₀, β)) ∈ (j '' Ioo α β)ᶜ
    rw [hfiber _ hTβ]
    exact hβC
  have heq : (range fun q => T (q, h q))ᶜ =
      ((π ⁻¹' ((j '' Ioo α β)ᶜ)) ∪ T '' Dminus) ∪ T '' Dplus := by
    ext x
    constructor
    · intro hx
      by_cases hxc : π x ∈ (j '' Ioo α β)ᶜ
      · exact Or.inl (Or.inl hxc)
      · have hxJ : π x ∈ j '' Ioo α β := not_not.mp hxc
        have hxTarget : x ∈ T.target := by
          rw [htarget]
          obtain ⟨s, hs, hsx⟩ := hxJ
          rw [mem_preimage, ← hsx]
          exact j.map_source (hjinner hs)
        have hz : T.symm x ∈ univ ×ˢ Ioo a b := hT ▸ T.map_target hxTarget
        rcases lt_trichotomy (T.symm x).2 (h (T.symm x).1) with hlo | he | hhi
        · exact Or.inl (Or.inr ⟨T.symm x, ⟨hz.2.1, hlo⟩, T.right_inv hxTarget⟩)
        · apply False.elim
          apply hx
          refine ⟨(T.symm x).1, ?_⟩
          change T ((T.symm x).1, h (T.symm x).1) = x
          rw [← he, Prod.mk.eta, T.right_inv hxTarget]
        · exact Or.inr ⟨T.symm x, ⟨hhi, hz.2.2⟩, T.right_inv hxTarget⟩
    · rintro ((hx | ⟨z, hz, rfl⟩) | ⟨z, hz, rfl⟩)
      · rintro ⟨q, rfl⟩
        exact hx ⟨h q, hrange q, (hfiber _ (hgraph q)).symm⟩
      · rintro ⟨q, hq⟩
        have he : (q, h q) = z := T.injOn (hgraph q) (hminusSub hz) hq
        have hs : z.2 = h z.1 := by rw [← he]
        exact (ne_of_lt hz.2) hs
      · rintro ⟨q, hq⟩
        have he : (q, h q) = z := T.injOn (hgraph q) (hplusSub hz) hq
        have hs : z.2 = h z.1 := by rw [← he]
        exact (ne_of_gt hz.1) hs
  rw [heq]
  exact IsConnected.union hmeetPlus (IsConnected.union hmeetMinus hzero hminus) hplus

end OpenPartialHomeomorph

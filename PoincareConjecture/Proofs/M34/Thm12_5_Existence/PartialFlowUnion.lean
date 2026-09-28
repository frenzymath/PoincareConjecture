import PoincareConjecture.Proofs.M34.Thm12_5_Existence.PartialFlowOrder
import PoincareConjecture.Proofs.M34.Standard.FlowLocality

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M34

theorem partialFlowChain_has_upper_bound {g0 : StandardInitialMetric}
    {c : Set (PartialStandardCapFlow g0)} (hc : IsChain partialFlowLE c)
    (hne : c.Nonempty) (hbdd : BddAbove ((fun F => F.lifetime) '' c)) :
    ∃ G : PartialStandardCapFlow g0, G.lifetime = sSup ((fun F => F.lifetime) '' c) ∧
      ∀ F ∈ c, partialFlowLE F G := by
  classical
  let L := (fun F : PartialStandardCapFlow g0 => F.lifetime) '' c
  let S := sSup L
  obtain ⟨F0, hF0⟩ := hne
  have hLne : L.Nonempty := ⟨F0.lifetime, F0, hF0, rfl⟩
  have hle (F : c) : F.val.lifetime ≤ S := le_csSup hbdd ⟨F.val, F.property, rfl⟩
  have hS : 0 < S := F0.lifetime_pos.trans_le (hle ⟨F0, hF0⟩)
  have hcover : ∀ t ∈ Ico 0 S, ∃ F : c, t ∈ Ico 0 F.val.lifetime := by
    intro t ht
    obtain ⟨T, ⟨F, hF, rfl⟩, htF⟩ := exists_lt_of_lt_csSup hLne ht.2
    exact ⟨⟨F, hF⟩, ht.1, htF⟩
  let index : ℝ → c := fun t =>
    if h : ∃ F : c, t ∈ Ico 0 F.val.lifetime then h.choose else ⟨F0, hF0⟩
  have hindex {t : ℝ} (ht : t ∈ Ico 0 S) :
      t ∈ Ico 0 (index t).val.lifetime := by
    dsimp [index]
    rw [dif_pos (hcover t ht)]
    exact (hcover t ht).choose_spec
  let data := fun t => partialFlowData (index t).val t
  have hmatch (F : c) {t : ℝ} (ht : t ∈ Ico 0 S)
      (htF : t ∈ Ico 0 F.val.lifetime) : data t = partialFlowData F.val t :=
    partialFlowData_eq_of_chain hc (index t).property F.property (hindex ht) htF
  let g := fun t => (data t).1
  let D := fun t => (data t).2
  have hnontrivial : (Ico 0 S).Nontrivial := by
    refine ⟨0, ⟨le_rfl, hS⟩, S / 2, ⟨by linarith, by linarith⟩, ?_⟩
    linarith
  have hloc : ∀ t ∈ Ico 0 S, ∃ K : Set ℝ, ∃ F : RicciFlow 3 StandardCapSpace K,
      t ∈ K ∧ K ∈ 𝓝[Ico 0 S] t ∧ g =ᶠ[𝓝[Ico 0 S] t] F.metric := by
    intro t ht
    obtain ⟨F, htF⟩ := hcover t ht
    have hK : Ico 0 F.val.lifetime ∈ 𝓝[Ico 0 S] t := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htF.2)] with s hs hs'
      exact ⟨hs.1, hs'⟩
    refine ⟨Ico 0 F.val.lifetime, F.val.flow, htF, hK, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hK] with s hs hsF
    exact congrArg Sigma.fst (hmatch F hs hsF)
  let G := flowOfLocalRepresentatives (Ico 0 S) g D ordConnected_Ico hnontrivial hloc
  have hzero := Sigma.mk.inj_iff.mp (hmatch ⟨F0, hF0⟩
    ⟨le_rfl, hS⟩ ⟨le_rfl, F0.lifetime_pos⟩)
  let U : PartialStandardCapFlow g0 := {
    lifetime := S
    lifetime_pos := hS
    flow := G
    initial_metric := hzero.1.trans F0.initial_metric
    initial_connection := hzero.2.trans F0.initial_connection
    curvature_locally_bounded := by
      intro T0 hT0 hT0S
      obtain ⟨F, htF⟩ := hcover T0 ⟨hT0, hT0S⟩
      obtain ⟨K, hK, hbound⟩ := F.val.curvature_locally_bounded T0 hT0 htF.2
      refine ⟨K, hK, fun t ht x => ?_⟩
      have heq := congrArg Sigma.fst (hmatch F
        ⟨ht.1, ht.2.trans_lt hT0S⟩ ⟨ht.1, ht.2.trans_lt htF.2⟩)
      have hnorm := curvatureTensorNorm_eq_of_metric_eq heq
        (G.connection t) (F.val.flow.connection t) x
      exact (congrArg abs hnorm).le.trans (hbound t ht x) }
  refine ⟨U, rfl, fun F hF => ⟨hle ⟨F, hF⟩, fun t ht => ?_⟩⟩
  exact (hmatch ⟨F, hF⟩ ⟨ht.1, ht.2.trans_le (hle ⟨F, hF⟩)⟩ ht).symm

end PoincareConjecture.M34

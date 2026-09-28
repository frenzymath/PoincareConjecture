import PoincareConjecture.Proofs.M76.Wall.ActualCutDomains
import PoincareConjecture.Proofs.M76.Wall.CompactMetrizableNeighborhood
import PoincareConjecture.Proofs.M76.Wall.CompactPLFrontierBicollar
import Mathlib.Topology.Metrizable.Uniformity

set_option autoImplicit false

open Set BrownCollar

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_protected_frontier_bicollar
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hF : IsCompact F)
    (hne : F.Nonempty) (hcut : Y ∩ frontier K = F) :
    ∃ U : Set X, IsOpen U ∧ F ⊆ U ∧ U ⊆ Y ∧
      ∃ H : (F × Ioo (-1 : ℝ) 1) ≃ₜ U,
        (∀ x, (H (bicollarBase x) : X) = (x : X)) ∧
        (∀ z, (H z : X) ∈ K ↔ 0 ≤ (z.2 : ℝ)) ∧
        ∀ z, (H z : X) ∈ F ↔ (z.2 : ℝ) = 0 := by
  have hFY : F ⊆ Y := hcut.symm.subset.trans inter_subset_left
  obtain ⟨N, hN, hFN, hNY, hmetric⟩ :=
    OpenPartialHomeomorph.exists_metrizable_open_neighborhood
      e hK.cover hK.compatible hF hY hFY
  let : TopologicalSpace.MetrizableSpace N := hmetric
  let : MetricSpace N := TopologicalSpace.metrizableSpaceMetric N
  have hNcut : N ∩ frontier K = F := by
    apply Subset.antisymm
    · intro x hx
      exact hcut.subset ⟨hNY hx.1, hx.2⟩
    · intro x hx
      exact ⟨hFN hx, (hcut.symm.subset hx).2⟩
  obtain ⟨d, hP, _, _, _, _, _, hfront, _, _, _, _, _⟩ :=
    exists_original_PL_cut_domains hK hN hNcut
  have hrange : F ⊆ range (Subtype.val : N → X) := by
    simpa only [Subtype.range_coe] using hFN
  have hcompact : IsCompact (frontier ((Subtype.val : N → X) ⁻¹' K)) := by
    rw [hfront]
    exact Topology.IsInducing.subtypeVal.isCompact_preimage' hF hrange
  have hnonempty : (frontier ((Subtype.val : N → X) ⁻¹' K)).Nonempty := by
    obtain ⟨x, hx⟩ := hne
    refine ⟨⟨x, hFN hx⟩, ?_⟩
    rw [hfront]
    exact hx
  obtain ⟨U0, hU0, hSU0, H0, hbase, hside, hzero⟩ :=
    hP.exists_compact_frontier_bicollar hcompact hnonempty
  let T : frontier ((Subtype.val : N → X) ⁻¹' K) ≃ₜ F :=
    (Homeomorph.setCongr hfront).trans
      (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hrange)
  have hT (x : frontier ((Subtype.val : N → X) ⁻¹' K)) :
      (T x : X) = ((x : N) : X) := rfl
  have hTi (x : F) : ((T.symm x : N) : X) = (x : X) := by
    exact (hT (T.symm x)).symm.trans
      (congrArg (Subtype.val : F → X) (T.apply_symm_apply x))
  let U : Set X := (Subtype.val : N → X) '' U0
  let J : U0 ≃ₜ U := Topology.IsEmbedding.subtypeVal.homeomorphImage U0
  let H : (F × Ioo (-1 : ℝ) 1) ≃ₜ U :=
    (T.symm.prodCongr (Homeomorph.refl (Ioo (-1 : ℝ) 1))).trans (H0.trans J)
  refine ⟨U, hN.isOpenMap_subtype_val _ hU0, ?_, ?_, H, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨⟨x, hFN hx⟩, hSU0 ?_, rfl⟩
    rw [hfront]
    exact hx
  · rintro x ⟨y, _, rfl⟩
    exact hNY y.property
  · intro x
    change ((H0 (bicollarBase (T.symm x)) : N) : X) = (x : X)
    exact (congrArg (Subtype.val : N → X) (hbase (T.symm x))).trans (hTi x)
  · intro z
    change ((H0 (T.symm z.1, z.2) : N) : X) ∈ K ↔ 0 ≤ (z.2 : ℝ)
    exact hside (T.symm z.1, z.2)
  · intro z
    change ((H0 (T.symm z.1, z.2) : N) : X) ∈ F ↔ (z.2 : ℝ) = 0
    have hmem (y : N) :
        y ∈ frontier ((Subtype.val : N → X) ⁻¹' K) ↔ (y : X) ∈ F :=
      Set.ext_iff.mp hfront y
    exact (hmem _).symm.trans (hzero (T.symm z.1, z.2))

end PoincareConjecture.M76

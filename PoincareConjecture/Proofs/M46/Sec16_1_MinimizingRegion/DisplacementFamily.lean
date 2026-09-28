import PoincareConjecture.Proofs.M14.Sec6_3_ParameterizedGaugeTube
import PoincareConjecture.Proofs.M14.Mathlib.FamilyCutoff










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




structure EndpointDisplacementFamily (gamma : ℝ → G.Point) (T b c : ℝ)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) (U : Set G.Point) where
  cutoff : ℝ → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_center : cutoff c = 1
  parameters : Set (EuclideanSpace ℝ (Fin n))
  parameters_open : IsOpen parameters
  zero_mem : 0 ∈ parameters
  family : ℝ × EuclideanSpace ℝ (Fin n) → G.Point
  smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
    (spacetimeModel n) ∞ family (Icc 0 b ×ˢ parameters)
  clock : ∀ s ∈ Icc 0 b, ∀ v ∈ parameters,
    G.spacetime.timeFunction (family (s, v)) = T - s ^ 2
  initial : ∀ v ∈ parameters, family (0, v) = gamma 0
  recovery : ∀ s ∈ Icc 0 b, family (s, 0) = gamma s
  target : ∀ s ∈ Icc 0 b, gamma s ∈ U → cutoff s ≠ 0 → ∀ q ∈ U,
    G.spacetime.timeFunction q = T - s ^ 2 →
    family (s, (cutoff s)⁻¹ • ((lift q).2.val - (lift (gamma s)).2.val)) = q




theorem endpointDisplacementFamily_nonempty {T b c : ℝ}
    (gamma : ℝ → G.Point) (hc : c ∈ Ioc 0 b)
    (hgamma : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ gamma (Icc 0 b))
    (hclock : ∀ s ∈ Icc 0 b, G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    (hliftClock : ∀ q ∈ U, (lift q).1.val = G.spacetime.timeFunction q)
    (hcenter : gamma c ∈ U) :
    Nonempty (EndpointDisplacementFamily gamma T b c j lift U) := by
  have hcC : c ∈ Icc 0 b := ⟨hc.1.le, hc.2⟩
  obtain ⟨O, hO, hcO, hOU⟩ := mem_nhdsWithin.mp
    ((hgamma c hcC).continuousWithinAt.preimage_mem_nhdsWithin (hU.mem_nhds hcenter))
  obtain ⟨chi, hsupport, _, hchi, _, hchic⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      ((hO.inter isOpen_Ioi).mem_nhds ⟨hcO, hc.1⟩)
  let f : ℝ × EuclideanSpace ℝ (Fin n) → G.Point := fun z => gamma z.1
  have hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n))))
      (spacetimeModel n) ∞ f (Icc 0 b ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) :=
    hgamma.comp contMDiff_fst.contMDiffOn (fun _ hz => hz.1)
  have hsrc : ∀ z ∈ Icc 0 b ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n))),
      z.1 ∈ tsupport chi → f z ∈ U := by
    intro z hz hs
    exact hOU ⟨(hsupport hs).1, hz.1⟩
  obtain ⟨N, hN, hzero, _, hshift⟩ := M14.exists_supportedGaugeTranslate_tube
    f j lift chi id isCompact_Icc isOpen_univ hf.continuousOn hlift.continuousOn
    hchi.continuous continuousOn_id hsrc (mem_univ (0 : EuclideanSpace ℝ (Fin n))) rfl
  let F := M14.supportedGaugeTranslateFamily f j lift chi id
  have hsrcN : ∀ z ∈ Icc 0 b ×ˢ N, z.1 ∈ tsupport chi → f z ∈ U :=
    fun z hz hs => hsrc z ⟨hz.1, mem_univ _⟩ hs
  refine ⟨{
    cutoff := chi
    cutoff_smooth := hchi
    cutoff_center := hchic
    parameters := N
    parameters_open := hN
    zero_mem := hzero
    family := F
    smooth := M14.supportedGaugeTranslateFamily_contMDiffOn f j lift chi id
      (hf.mono (fun _ hz => ⟨hz.1, mem_univ _⟩)) hU hlift hright hchi
      contDiffOn_id hsrcN hshift
    clock := ?_
    initial := ?_
    recovery := ?_
    target := ?_ }⟩
  · intro s hs v hv
    exact (M14.supportedGaugeTranslateFamily_time f j lift chi id
      (fun ht => hright _ (hsrcN (s, v) ⟨hs, hv⟩ ht))).trans (hclock s hs)
  · intro v _
    exact M14.supportedGaugeTranslateFamily_eq_of_not_tsupport f j lift chi id
      (fun hs => (lt_irrefl (0 : ℝ)) (hsupport hs).2)
  · intro s hs
    by_cases ht : s ∈ tsupport chi
    · exact M14.supportedGaugeTranslateFamily_eq_of_zero f j lift chi id
        (hright _ (hsrcN (s, 0) ⟨hs, hzero⟩ ht)) rfl
    · exact M14.supportedGaugeTranslateFamily_eq_of_not_tsupport f j lift chi id ht
  · intro s hs hgs hchis q hq hqt
    have hshiftval : (lift (gamma s)).2.val +
        chi s • ((chi s)⁻¹ • ((lift q).2.val - (lift (gamma s)).2.val)) = (lift q).2.val := by
      rw [smul_smul, mul_inv_cancel₀ hchis, one_smul, add_comm, sub_add_cancel]
    have hshiftpoint : (G.gaugeCover.spatial j).affineShift (lift (gamma s)).2
        (chi s • ((chi s)⁻¹ • ((lift q).2.val - (lift (gamma s)).2.val))) = (lift q).2 := by
      have hm : (lift (gamma s)).2.val +
          chi s • ((chi s)⁻¹ • ((lift q).2.val - (lift (gamma s)).2.val)) ∈
          G.gaugeCover.spatial j := by
        rw [hshiftval]
        exact (lift q).2.property
      apply Subtype.ext
      rw [(G.gaugeCover.spatial j).affineShift_val hm, hshiftval]
    have ht : (lift (gamma s)).1 = (lift q).1 := by
      apply Subtype.ext
      rw [hliftClock _ hgs, hliftClock _ hq, hclock s hs, hqt]
    change M14.supportedGaugeTranslateFamily f j lift chi id _ = q
    rw [M14.supportedGaugeTranslateFamily_eq_gauge f j lift chi id (hright _ hgs)]
    change (G.gaugeCover.cylinder j).toSpacetime ((lift (gamma s)).1,
      (G.gaugeCover.spatial j).affineShift (lift (gamma s)).2 _) = q
    dsimp only [id_eq, Prod.fst, Prod.snd]
    rw [hshiftpoint, ht]
    exact hright q hq

end PoincareConjecture.Proofs.M46

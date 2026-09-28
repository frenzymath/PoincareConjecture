import PoincareConjecture.Proofs.M14.Sec6_3_ParameterizedGaugeTube
import PoincareConjecture.Proofs.M14.Mathlib.FamilyCutoff

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {P : Type v} [NormedAddCommGroup P] [NormedSpace ℝ P]

structure GaugeEndpointFamily (f : ℝ × P → G.Point) (U : Set P) (T a b c : ℝ) (p₀ : P)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) where
  family : ℝ × (P × EuclideanSpace ℝ (Fin n)) → G.Point
  parameters : Set (P × EuclideanSpace ℝ (Fin n))
  parameters_open : IsOpen parameters
  center_mem : (p₀, (lift (f (c, p₀))).2.val) ∈ parameters
  parameter_subset : ∀ z ∈ parameters, z.1 ∈ U
  smooth : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P × EuclideanSpace ℝ (Fin n))))
    (spacetimeModel n) ∞ family (Icc a b ×ˢ parameters)
  clock : ∀ s ∈ Icc a b, ∀ z ∈ parameters,
    G.spacetime.timeFunction (family (s, z)) = T - s ^ 2
  initial : ∀ z ∈ parameters, family (a, z) = f (a, z.1)
  final : ∀ z ∈ parameters, family (b, z) = f (b, z.1)
  marked : ∀ z ∈ parameters, ∃ hy : z.2 ∈ G.gaugeCover.spatial j,
    family (c, z) = (G.gaugeCover.cylinder j).toSpacetime
      ((lift (f (c, p₀))).1, ⟨z.2, hy⟩)
  recovery : ∀ z ∈ parameters, ∀ s ∈ Icc a b,
    family (s, (z.1, (lift (f (c, z.1))).2.val)) = f (s, z.1)
  coordinate_smooth : ContDiffAt ℝ ∞ (fun r => (lift (f (c, r))).2.val) p₀

theorem gaugeEndpointFamily_nonempty (f : ℝ × P → G.Point) {U : Set P}
    {T a b c : ℝ} {p₀ : P} (hU : IsOpen U) (hp : p₀ ∈ U) (hc : c ∈ Ioo a b)
    (hf : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) (spacetimeModel n) ∞ f (Icc a b ×ˢ U))
    (hclock : ∀ s ∈ Icc a b, ∀ r ∈ U, G.spacetime.timeFunction (f (s, r)) = T - s ^ 2)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) {V : Set G.Point} (hV : IsOpen V)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift V)
    (hright : ∀ q ∈ V, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    (hcenter : f (c, p₀) ∈ V) : Nonempty (GaugeEndpointFamily f U T a b c p₀ j lift) := by
  have hcC : c ∈ Icc a b := Ioo_subset_Icc_self hc
  have hnear : Icc a b ×ˢ U ∈ 𝓝 (c, p₀) :=
    mem_of_superset ((isOpen_Ioo.prod hU).mem_nhds ⟨hc, hp⟩)
      (fun _ hz => ⟨Ioo_subset_Icc_self hz.1, hz.2⟩)
  obtain ⟨N₀, hN₀, hpN₀, χ, hχ, hχc, hsupport, hband⟩ :=
    exists_family_time_cutoff ((hf (c, p₀) ⟨hcC, hp⟩).continuousWithinAt.continuousAt hnear)
      hV hcenter isOpen_Ioo hc
  let D := U ∩ N₀
  have hD : IsOpen D := hU.inter hN₀
  have hpD : p₀ ∈ D := ⟨hp, hpN₀⟩
  have hcS : c ∈ tsupport χ := subset_tsupport χ (by
    change χ c ≠ 0
    rw [hχc]
    exact one_ne_zero)
  have hFc : ContMDiffOn (𝓘(ℝ, P)) (spacetimeModel n) ∞ (fun r => f (c, r)) D :=
    hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ hr => ⟨hcC, hr.1⟩)
  have hL : ContMDiffOn (𝓘(ℝ, P)) (spacetimeModel n) ∞ (fun r => lift (f (c, r))) D :=
    hlift.comp hFc (fun r hr => hband c hcS r hr.2)
  let A := fun r => (lift (f (c, r))).2.val
  have hA : ContDiffOn ℝ ∞ A D :=
    (contMDiff_subtype_val.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn hL)).contDiffOn
  let F := fun z : ℝ × (P × EuclideanSpace ℝ (Fin n)) => f (z.1, z.2.1)
  let d := fun z : P × EuclideanSpace ℝ (Fin n) => z.2 - A z.1
  let B := D ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))
  have hB : IsOpen B := hD.prod isOpen_univ
  have hk : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P × EuclideanSpace ℝ (Fin n))))
      ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P))) ∞
      (fun z : ℝ × (P × EuclideanSpace ℝ (Fin n)) => (z.1, z.2.1)) := by
    rw [← modelWithCornersSelf_prod, ← modelWithCornersSelf_prod,
      chartedSpaceSelf_prod, chartedSpaceSelf_prod]
    exact (contDiff_fst.prodMk contDiff_snd.fst).contMDiff
  have hF : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P × EuclideanSpace ℝ (Fin n))))
      (spacetimeModel n) ∞ F (Icc a b ×ˢ B) :=
    hf.comp hk.contMDiffOn (fun _ hz => ⟨hz.1, hz.2.1.1⟩)
  have hd : ContDiffOn ℝ ∞ d B :=
    contDiffOn_snd.sub (hA.comp contDiffOn_fst (fun _ hz => hz.1))
  have hsrc : ∀ z ∈ Icc a b ×ˢ B, z.1 ∈ tsupport χ → F z ∈ V :=
    fun z hz hs => hband z.1 hs z.2.1 hz.2.1.2
  obtain ⟨N, hN, hpN, hNB, hshift⟩ := exists_supportedGaugeTranslate_tube F j lift χ d
    isCompact_Icc hB hF.continuousOn hlift.continuousOn hχ.continuous hd.continuousOn hsrc
    (show (p₀, A p₀) ∈ B from ⟨hpD, mem_univ _⟩) (by exact sub_self _)
  let H := supportedGaugeTranslateFamily F j lift χ d
  have hsrcN : ∀ z ∈ Icc a b ×ˢ N, z.1 ∈ tsupport χ → F z ∈ V :=
    fun z hz hs => hsrc z ⟨hz.1, hNB hz.2⟩ hs
  have hH : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, P × EuclideanSpace ℝ (Fin n))))
      (spacetimeModel n) ∞ H (Icc a b ×ˢ N) :=
    supportedGaugeTranslateFamily_contMDiffOn F j lift χ d
      (hF.mono (fun _ hz => ⟨hz.1, hNB hz.2⟩)) hV hlift hright hχ (hd.mono hNB) hsrcN hshift
  have htime (r : P) (hr : r ∈ D) : (lift (f (c, r))).1.val = T - c ^ 2 :=
    ((G.gaugeCover.cylinder j).time_eq (lift (f (c, r)))).symm.trans
      ((congrArg G.spacetime.timeFunction (hright _ (hband c hcS r hr.2))).trans
        (hclock c hcC r hr.1))
  refine ⟨{
    family := H
    parameters := N
    parameters_open := hN
    center_mem := hpN
    parameter_subset := fun _ hz => (hNB hz).1.1
    smooth := hH
    clock := ?_
    initial := ?_
    final := ?_
    marked := ?_
    recovery := ?_
    coordinate_smooth := (hA p₀ hpD).contDiffAt (hD.mem_nhds hpD) }⟩
  · intro s hs z hz
    exact (supportedGaugeTranslateFamily_time F j lift χ d
      (fun ht => hright _ (hsrcN (s, z) ⟨hs, hz⟩ ht))).trans
        (hclock s hs z.1 (hNB hz).1.1)
  · intro z _
    exact supportedGaugeTranslateFamily_eq_of_not_tsupport F j lift χ d
      (fun hs => (lt_irrefl a) (hsupport hs).1)
  · intro z _
    exact supportedGaugeTranslateFamily_eq_of_not_tsupport F j lift χ d
      (fun hs => (lt_irrefl b) (hsupport hs).2)
  · intro z hz
    have hy := hshift (c, z) ⟨hcC, hz⟩ hcS
    change (lift (f (c, z.1))).2.val + χ c • (z.2 - (lift (f (c, z.1))).2.val) ∈
      G.gaugeCover.spatial j at hy
    rw [hχc, one_smul, add_comm, sub_add_cancel] at hy
    have ht : (lift (f (c, z.1))).1 = (lift (f (c, p₀))).1 :=
      Subtype.ext ((htime z.1 (hNB hz).1).trans (htime p₀ hpD).symm)
    refine ⟨hy, ?_⟩
    have hmark := supportedGaugeTranslateFamily_eq_target F j lift χ d
      (hright _ (hsrcN (c, z) ⟨hcC, hz⟩ hcS)) hχc ⟨z.2, hy⟩ (by rfl)
    exact hmark.trans (congrArg (fun t => (G.gaugeCover.cylinder j).toSpacetime (t, ⟨z.2, hy⟩)) ht)
  · intro z hz s _
    by_cases hs : s ∈ tsupport χ
    · exact supportedGaugeTranslateFamily_eq_of_zero F j lift χ d
        (hright _ (hband s hs z.1 (hNB hz).1.2)) (sub_self _)
    · exact supportedGaugeTranslateFamily_eq_of_not_tsupport F j lift χ d hs

end PoincareConjecture.M14

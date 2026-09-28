import PoincareConjecture.Proofs.M39.Prop15_12_ExtensionData
import PoincareConjecture.Proofs.M39.Prop15_12_MapConstruction
import PoincareConjecture.Proofs.M39.Prop15_12_LocalLipschitz
import PoincareConjecture.Proofs.M39.Prop15_12_LocalEmbedding











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M39

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  (I : RepairedComparisonMapInput D T hT)

local notation "E" => D.flow.event T hT



theorem comparisonLimit_contMDiffAt {x : I.parent.carrier.carrier}
    (hx : I.parent.inclusion x ∈ (E).regular_limit) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞
      ((E).limit_identify.map ∘ I.parent.inclusion) x := by
  exact (((E).limit_identify.map_smooth _ hx).contMDiffAt
    ((E).regular_limit_open.mem_nhds hx)).comp x (I.parent.inclusion_smooth x)



theorem comparisonLimit_metric_le
    (t : Set.Ico (E).tMinus T) {C : ℝ} {K : Set (D.flow.slice (E).tMinus).carrier}
    (hK : K ⊆ (E).regular_limit)
    (hmetric : ∀ z ∈ K, ∀ w : TangentSpace (𝓡 3) z,
      (E).limit_metric.inner ((E).limit_identify.map z)
        (mfderiv (𝓡 3) (𝓡 3) (E).limit_identify.map z w)
        (mfderiv (𝓡 3) (𝓡 3) (E).limit_identify.map z w) ≤
        C ^ 2 * ((E).pre_flow.metric t.1).inner z w w)
    {x : I.parent.carrier.carrier} (hx : I.parent.inclusion x ∈ K)
    (v : TangentSpace (𝓡 3) x) :
    (E).limit_metric.inner (((E).limit_identify.map ∘ I.parent.inclusion) x)
      (mfderiv (𝓡 3) (𝓡 3) ((E).limit_identify.map ∘ I.parent.inclusion) x v)
      (mfderiv (𝓡 3) (𝓡 3) ((E).limit_identify.map ∘ I.parent.inclusion) x v) ≤
      C ^ 2 * (I.parent_metric t.1).inner x v v := by
  have hreg := hK hx
  have hmap := ((E).limit_identify.map_smooth _ hreg).contMDiffAt
    ((E).regular_limit_open.mem_nhds hreg)
  rw [mfderiv_comp x (hmap.mdifferentiableAt (by simp))
    (I.parent.inclusion_smooth.mdifferentiable (by simp) x)]
  change (E).limit_metric.inner ((E).limit_identify.map (I.parent.inclusion x))
    (mfderiv (𝓡 3) (𝓡 3) (E).limit_identify.map (I.parent.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x v))
    (mfderiv (𝓡 3) (𝓡 3) (E).limit_identify.map (I.parent.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x v)) ≤ _
  have hb := hmetric _ hx (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion x v)
  rwa [I.parent_pullback t] at hb





theorem comparisonExtension_edist_le (G : ComparisonExtension I)
    (t : Set.Ico (E).tMinus T) {C : ℝ} (hC : 0 < C)
    (hmetric : ∀ z ∈ G.control, ∀ w : TangentSpace (𝓡 3) z,
      (E).limit_metric.inner ((E).limit_identify.map z)
        (mfderiv (𝓡 3) (𝓡 3) (E).limit_identify.map z w)
        (mfderiv (𝓡 3) (𝓡 3) (E).limit_identify.map z w) ≤
        C ^ 2 * ((E).pre_flow.metric t.1).inner z w w)
    (x y : I.parent.carrier.carrier) :
    I.child_metric.edist (G.map x) (G.map y) ≤
      ENNReal.ofReal C * (I.parent_metric t.1).edist x y := by
  choose U hU hxU hlocal using G.local_model
  apply metric_edist_le_mul_of_open_cover (I.parent_metric t.1) I.child_metric
    U hU (fun z => ⟨z, hxU z⟩) G.map hC
  intro j γ a b hab hγ hγU
  rcases hlocal j with ⟨z, heq⟩ | ⟨hcontrol, hret | ⟨i, hchild, hneck, heq⟩⟩
  · rw [heq (hγU ⟨le_rfl, hab⟩), heq (hγU ⟨hab, le_rfl⟩),
      M36.metric_edist_self]
    exact zero_le
  · apply edist_comp_le_mul_pathELength (I.parent_metric t.1) I.child_metric hC
      (fun z hz => ((extension_retained_smooth I G.retained_agreement) z
        (hret hz)).contMDiffAt (I.retained_open.mem_nhds (hret hz)))
      (fun z hz v => ?_) hab hγ hγU
    rw [extension_retained_metric I G.retained_agreement z (hret hz)]
    have hb := hmetric _ (hcontrol hz)
      (mfderiv (𝓡 3) (𝓡 3) I.parent.inclusion z v)
    rwa [I.parent_pullback t] at hb
  · rw [heq (hγU ⟨le_rfl, hab⟩), heq (hγU ⟨hab, le_rfl⟩)]
    exact edist_comp_le_mul_pathELength_of_intrinsic_bound
      (I.parent_metric t.1) (E).limit_metric I.child_metric
      (f := (E).limit_identify.map ∘ I.parent.inclusion)
      (c := localChildEmbedding E i I.child ∘ ((E).local_result i).collapse) hC
      (fun z hz => comparisonLimit_contMDiffAt I (G.control_regular (hcontrol hz)))
      (fun z hz v => comparisonLimit_metric_le I t G.control_regular hmetric
        (hcontrol hz) v) hneck
      (fun z hz w hw => localChildCollapse_edist_le E i I.child hchild
        I.child_metric I.child_pullback z hz w hw) hab hγ hγU




theorem comparisonExtension_late_lipschitz (G : ComparisonExtension I)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℝ, 0 < d ∧ d ≤ T - (E).tMinus ∧
      ∀ t : ℝ, T - d < t → t < T → ∀ x y,
        I.child_metric.edist (G.map x) (G.map y) ≤
          ENNReal.ofReal (1 + eta) * (I.parent_metric t).edist x y := by
  have hC : 0 < 1 + eta := by linarith
  have hsq : 1 < (1 + eta) ^ 2 := by nlinarith [sq_nonneg eta]
  have hlim := metricLimit_eventually_compact_comparison (E).limit_identify
    (E).regular_limit_open (E).metric_converges G.control_compact G.control_regular hsq
  obtain ⟨s, hs, hbound⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hlim
  let d := min (T - s) (T - (E).tMinus)
  have hd : 0 < d := lt_min (sub_pos.mpr hs) (sub_pos.mpr (E).tMinus_lt)
  have hds : d ≤ T - s := min_le_left _ _
  have hdt : d ≤ T - (E).tMinus := min_le_right _ _
  refine ⟨d, hd, hdt, ?_⟩
  intro t ht htT x y
  have htpre : (E).tMinus ≤ t := by linarith
  have hts : s < t := by linarith
  exact comparisonExtension_edist_le I G ⟨t, htpre, htT⟩ hC (hbound ⟨hts, htT⟩) x y




noncomputable def comparisonConclusionOfExtension (G : ComparisonExtension I) :
    RepairedComparisonMapConclusion I where
  map := G.map
  target_basepoint := G.map I.parent.basepoint
  based := rfl
  retained_agreement := G.retained_agreement
  retained_open := I.retained_open
  retained_target_open := extension_retained_target_open I G.retained_agreement
  retained_smooth := extension_retained_smooth I G.retained_agreement
  retained_metric := extension_retained_metric I G.retained_agreement
  distance_window := T - (E).tMinus
  distance_window_pos := sub_pos.mpr (E).tMinus_lt
  distance_window_le := le_rfl
  outside_image_in_caps := G.outside_image_in_caps
  late_lipschitz := comparisonExtension_late_lipschitz I G

end PoincareConjecture.M39

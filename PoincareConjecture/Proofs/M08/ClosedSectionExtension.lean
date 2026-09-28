import PoincareConjecture.Proofs.M08.SmoothSectionExtension
import PoincareConjecture.Proofs.M08.SmoothEndpointExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def gluedClosedParametricSectionExtension {ι : Type v} {C : Set ℝ}
    (O : TopologicalSpace.Opens ℝ) (hCO : C ⊆ O)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) O univ)
    (V : ι → Set ℝ) (α : ℝ → M) (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (E : ∀ i, ParametricAlongCurveExtensionOn (C ∩ V i) α Y)
    (hgraph : ∀ i s, s ∈ V i → (s, α s) ∈ (E i).domain)
    (hρ : ρ.IsSubordinate (fun i ↦ (Subtype.val : O → ℝ) ⁻¹' V i)) :
    ParametricAlongCurveExtensionOn C α Y where
  extension := parametricWeightedSum O ρ (fun i ↦ (E i).extension)
  domain := curveGluingDomain O ρ (fun i ↦ (E i).domain)
  open_domain := curveGluingDomain_open O ρ _ (fun i ↦ (E i).open_domain)
  graph_mem s hs := curveGluingDomain_graph_mem O ρ _ α
    (fun t i ht ↦ hgraph i t (hρ i ht)) ⟨s, hCO hs⟩
  smooth z hz := by
    rcases hz with ⟨⟨s, x⟩, hz, rfl⟩
    have hdomain := (mem_curveGluingRelativeDomain O ρ (fun i ↦ (E i).domain)).mp hz
    have hpieces : ∀ i ∈ ρ.fintsupport s,
        ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
          (fun w : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2
            (timePartitionWeight O ρ i w.1 • (E i).extension w.1 w.2)) ((s : ℝ), x) := by
      intro i hi
      exact parametricExtension_contMDiffAt_smul_reparam (E i) (f := id)
        (hdomain i ((ρ.mem_fintsupport_iff s i).mp hi)) contDiffAt_id
        (timePartitionWeight_contDiffAt O ρ i s)
    have hsum := contMDiffAt_sum_parametric (ρ.fintsupport s)
      (fun i r y ↦ timePartitionWeight O ρ i r • (E i).extension r y) hpieces
    apply ContMDiffAt.contMDiffWithinAt
    apply hsum.congr_of_eventuallyEq
    have hnear : ∀ᶠ w : ℝ × M in 𝓝 ((s : ℝ), x), ∀ y : M,
        parametricWeightedSum O ρ (fun i ↦ (E i).extension) w.1 y =
          ∑ i ∈ ρ.fintsupport s, timePartitionWeight O ρ i w.1 •
            (E i).extension w.1 y :=
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : ℝ × M → ℝ)
        ((s : ℝ), x)).eventually
          (parametricWeightedSum_eventually_eq_sum O ρ (fun i ↦ (E i).extension) s)
    filter_upwards [hnear] with w hw
    exact congrArg (fun v : TangentSpace (𝓡 n) w.2 ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2 v) (hw w.2)
  agrees t ht := by
    let s : O := ⟨t, hCO ht⟩
    have hS := (timePartitionWeight_eventually_support_subset O ρ s).self_of_nhds
    rw [parametricWeightedSum_eq_sum O ρ (fun i ↦ (E i).extension) (α t) hS]
    calc
      (∑ i ∈ ρ.fintsupport s, timePartitionWeight O ρ i t • (E i).extension t (α t)) =
          ∑ i ∈ ρ.fintsupport s, timePartitionWeight O ρ i t • Y t := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(E i).agrees t ⟨ht, hρ i ((ρ.mem_fintsupport_iff s i).mp hi)⟩]
      _ = (∑ i ∈ ρ.fintsupport s, timePartitionWeight O ρ i t) • Y t :=
        (Finset.sum_smul ..).symm
      _ = Y t := by rw [timePartitionWeight_sum_eq_one O ρ s hS, one_smul]

theorem exists_closedSectionExtension_of_local {C : Set ℝ}
    (α : ℝ → M) (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hloc : ∀ s ∈ C, ∃ V : Set ℝ, IsOpen V ∧ s ∈ V ∧
      ∃ E : ParametricAlongCurveExtensionOn (C ∩ V) α Y,
        ∀ t ∈ V, (t, α t) ∈ E.domain) :
    Nonempty (ParametricAlongCurveExtensionOn C α Y) := by
  classical
  choose V hV hsV E hgraph using fun s : C ↦ hloc s s.property
  let O : TopologicalSpace.Opens ℝ := ⟨⋃ i : C, V i, isOpen_iUnion hV⟩
  have hCO : C ⊆ O := fun s hs ↦ mem_iUnion.mpr ⟨⟨s, hs⟩, hsV ⟨s, hs⟩⟩
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  have hcover : (univ : Set O) ⊆ ⋃ i : C, (Subtype.val : O → ℝ) ⁻¹' V i := by
    intro s _
    obtain ⟨i, hi⟩ := mem_iUnion.mp s.property
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity C (𝓘(ℝ, ℝ)) O univ,
      ρ.IsSubordinate (fun i ↦ (Subtype.val : O → ℝ) ⁻¹' V i) :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ)) isClosed_univ _
      (fun i ↦ (hV i).preimage continuous_subtype_val) hcover
  exact ⟨gluedClosedParametricSectionExtension O hCO ρ V α Y E hgraph hρ⟩

set_option maxHeartbeats 1000000 in
theorem exists_local_closedSectionExtension {a b : ℝ} (hab : a < b)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s)) (Icc a b))
    {s : ℝ} (hs : s ∈ Icc a b) :
    ∃ V : Set ℝ, IsOpen V ∧ s ∈ V ∧
      ∃ E : ParametricAlongCurveExtensionOn (Icc a b ∩ V) α Y,
        ∀ t ∈ V, (t, α t) ∈ E.domain := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (α s)
  have hnear : U ∩ α ⁻¹' e.baseSet ∈ 𝓝 s := by
    refine inter_mem (hU.mem_nhds (hCU hs)) ?_
    exact ((hα s (hCU hs)).contMDiffAt (hU.mem_nhds (hCU hs))).continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))
  obtain ⟨l, r, ⟨hls, hsr⟩, hchart⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let l' := (l + s) / 2
  let r' := (s + r) / 2
  let c := max a l'
  let d := min b r'
  have hll : l < l' := by dsimp only [l']; linarith
  have hls' : l' < s := by dsimp only [l']; linarith
  have hsr' : s < r' := by dsimp only [r']; linarith
  have hrr : r' < r := by dsimp only [r']; linarith
  have hcd : c < d := max_lt
    (lt_min hab (hs.1.trans_lt hsr'))
    (lt_min (hls'.trans_le hs.2) (hls'.trans hsr'))
  have hsub : Icc c d ⊆ Icc a b :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ t ∈ Icc c d, α t ∈ e.baseSet := by
    intro t ht
    exact (hchart ⟨hll.trans_le ((le_max_right _ _).trans ht.1),
      (ht.2.trans (min_le_right _ _)).trans_lt hrr⟩).2
  let y := fun t ↦ (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α t) (Y t))).2
  have hpair := e.contMDiffOn.comp (hY.mono hsub)
    (fun t ht ↦ e.mem_source.mpr (hsrc t ht))
  have hy : ContDiffOn ℝ ∞ y (Icc c d) :=
    ContMDiffOn.contDiffOn (fun t ht ↦ (hpair t ht).snd)
  obtain ⟨g, hg, hgy⟩ := exists_smooth_extension_Icc hcd y hy
  let V := Ioo l' r'
  have hVsrc : ∀ t ∈ V, α t ∈ e.baseSet := fun t ht ↦
    (hchart ⟨hll.trans ht.1, ht.2.trans hrr⟩).2
  have hVsub : Icc a b ∩ V ⊆ Icc c d := fun t ht ↦
    ⟨max_le ht.1.1 ht.2.1.le, le_min ht.1.2 ht.2.2.le⟩
  let E : ParametricAlongCurveExtensionOn (Icc a b ∩ V) α Y :=
    parametricExtensionInChart e g isOpen_Ioo inter_subset_right
      (fun t ht ↦ hVsrc t ht.2) hg.contMDiff.contMDiffOn (by
        intro t ht
        rw [hgy (hVsub ht)]
        exact e.symm_apply_apply_mk (hVsrc t ht.2) (Y t))
  exact ⟨V, isOpen_Ioo, ⟨hls', hsr'⟩, E, fun t ht ↦ ⟨ht, hVsrc t ht⟩⟩

theorem exists_closedSectionExtension {a b : ℝ} (hab : a < b)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s)) (Icc a b)) :
    Nonempty (ParametricAlongCurveExtensionOn (Icc a b) α Y) :=
  exists_closedSectionExtension_of_local α Y
    (fun _ hs ↦ exists_local_closedSectionExtension hab hU hCU α hα Y hY hs)

end PoincareConjecture.M08

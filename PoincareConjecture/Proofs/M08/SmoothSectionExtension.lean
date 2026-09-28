import PoincareConjecture.Proofs.M08.GlobalCurveExtension
import PoincareConjecture.Proofs.M08.ChartExtensions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def restrictParametricSectionExtension {I U : Set ℝ} {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)} (hsub : I ⊆ U)
    (E : ParametricAlongCurveExtensionOn U α Y) : ParametricAlongCurveExtensionOn I α Y where
  extension := E.extension
  domain := E.domain
  open_domain := E.open_domain
  graph_mem s hs := E.graph_mem s (hsub hs)
  smooth := E.smooth
  agrees s hs := E.agrees s (hsub hs)

def gluedParametricSectionExtension {ι : Type v} (I : TopologicalSpace.Opens ℝ)
    (ρ : SmoothPartitionOfUnity ι (𝓘(ℝ, ℝ)) I univ)
    (U : ι → Set ℝ) (α : ℝ → M) (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (E : ∀ i, ParametricAlongCurveExtensionOn (U i) α Y)
    (hρ : ρ.IsSubordinate (fun i ↦ (Subtype.val : I → ℝ) ⁻¹' U i)) :
    ParametricAlongCurveExtensionOn (I : Set ℝ) α Y where
  extension := parametricWeightedSum I ρ (fun i ↦ (E i).extension)
  domain := curveGluingDomain I ρ (fun i ↦ (E i).domain)
  open_domain := curveGluingDomain_open I ρ _ (fun i ↦ (E i).open_domain)
  graph_mem s hs := curveGluingDomain_graph_mem I ρ _ α
    (fun t i ht ↦ (E i).graph_mem t (hρ i ht)) ⟨s, hs⟩
  smooth z hz := by
    rcases hz with ⟨⟨s, x⟩, hz, rfl⟩
    have hdomain := (mem_curveGluingRelativeDomain I ρ (fun i ↦ (E i).domain)).mp hz
    have hpieces : ∀ i ∈ ρ.fintsupport s,
        ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
          (fun w : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2
            (timePartitionWeight I ρ i w.1 • (E i).extension w.1 w.2)) ((s : ℝ), x) := by
      intro i hi
      exact parametricExtension_contMDiffAt_smul_reparam (E i) (f := id)
        (hdomain i ((ρ.mem_fintsupport_iff s i).mp hi)) contDiffAt_id
        (timePartitionWeight_contDiffAt I ρ i s)
    have hsum := contMDiffAt_sum_parametric (ρ.fintsupport s)
      (fun i r y ↦ timePartitionWeight I ρ i r • (E i).extension r y) hpieces
    apply ContMDiffAt.contMDiffWithinAt
    apply hsum.congr_of_eventuallyEq
    have hnear : ∀ᶠ w : ℝ × M in 𝓝 ((s : ℝ), x), ∀ y : M,
        parametricWeightedSum I ρ (fun i ↦ (E i).extension) w.1 y =
          ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i w.1 •
            (E i).extension w.1 y :=
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : ℝ × M → ℝ)
        ((s : ℝ), x)).eventually
          (parametricWeightedSum_eventually_eq_sum I ρ (fun i ↦ (E i).extension) s)
    filter_upwards [hnear] with w hw
    exact congrArg (fun v : TangentSpace (𝓡 n) w.2 ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2 v) (hw w.2)
  agrees t ht := by
    let s : I := ⟨t, ht⟩
    have hS := (timePartitionWeight_eventually_support_subset I ρ s).self_of_nhds
    rw [parametricWeightedSum_eq_sum I ρ (fun i ↦ (E i).extension) (α t) hS]
    calc
      (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i t • (E i).extension t (α t)) =
          ∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i t • Y t := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(E i).agrees t (hρ i ((ρ.mem_fintsupport_iff s i).mp hi))]
      _ = (∑ i ∈ ρ.fintsupport s, timePartitionWeight I ρ i t) • Y t :=
        (Finset.sum_smul ..).symm
      _ = Y t := by rw [timePartitionWeight_sum_eq_one I ρ s hS, one_smul]

theorem exists_parametricSectionExtension_of_local {I : Set ℝ} (hI : IsOpen I)
    (α : ℝ → M) (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hloc : ∀ s ∈ I, ∃ U : Set ℝ, IsOpen U ∧ s ∈ U ∧
      Nonempty (ParametricAlongCurveExtensionOn U α Y)) :
    Nonempty (ParametricAlongCurveExtensionOn I α Y) := by
  classical
  let O : TopologicalSpace.Opens ℝ := ⟨I, hI⟩
  let : LocallyCompactSpace O := O.isOpen.locallyCompactSpace
  choose U hU hsU hE using fun s : O ↦ hloc s s.property
  let E := fun s : O ↦ Classical.choice (hE s)
  have hcover : (univ : Set O) ⊆ ⋃ i : O, (Subtype.val : O → ℝ) ⁻¹' U i := by
    intro s _
    exact mem_iUnion.mpr ⟨s, hsU s⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : SmoothPartitionOfUnity O (𝓘(ℝ, ℝ)) O univ,
      ρ.IsSubordinate (fun i ↦ (Subtype.val : O → ℝ) ⁻¹' U i) :=
    SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, ℝ)) isClosed_univ _
      (fun i ↦ (hU i).preimage continuous_subtype_val) hcover
  exact ⟨gluedParametricSectionExtension O ρ U α Y E hρ⟩

theorem exists_parametricSectionExtension {I : Set ℝ} (hI : IsOpen I)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α I)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s) (Y s)) I) :
    Nonempty (ParametricAlongCurveExtensionOn I α Y) := by
  apply exists_parametricSectionExtension_of_local hI α Y
  intro s hs
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (α s)
  let U := I ∩ α ⁻¹' e.baseSet
  have hU : IsOpen U := hα.continuousOn.isOpen_inter_preimage hI e.open_baseSet
  have hsU : s ∈ U := ⟨hs, show α s ∈ e.baseSet from
    mem_baseSet_trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) (α s)⟩
  let y := fun r ↦ (e (Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α r) (Y r))).2
  have hpair := e.contMDiffOn.comp (hY.mono inter_subset_left)
    (fun r hr ↦ e.mem_source.mpr hr.2)
  have hy : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ y U := fun r hr ↦ (hpair r hr).snd
  refine ⟨U, hU, hsU, ⟨parametricExtensionInChart e y hU Subset.rfl
    (fun r hr ↦ hr.2) hy ?_⟩⟩
  intro r hr
  exact e.symm_apply_apply_mk hr.2 (Y r)

end PoincareConjecture.M08

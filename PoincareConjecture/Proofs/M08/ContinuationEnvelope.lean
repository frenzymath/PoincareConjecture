import PoincareConjecture.Proofs.M08.ContinuationCurve

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T2Space M]

theorem continuationCurve_eqOn_of_tail {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {d e c b : ℝ}
    (hd : 0 ≤ d) (he : 0 ≤ e) (hdc : d < c) (hec : e < c) (hcb : c < b)
    (htime : ∀ s ∈ Ioo 0 b, T - s ^ 2 ∈ J) {α β γ : ℝ → M}
    (hα : IsContinuationCurve F T α (Ioo d b))
    (hβ : IsContinuationCurve F T β (Ioo e b))
    (hαγ : EqOn α γ (Ioo c b)) (hβγ : EqOn β γ (Ioo c b)) :
    EqOn α β (Ioo (max d e) b) := by
  have hsubd : Ioo (max d e) b ⊆ Ioo d b := Ioo_subset_Ioo (le_max_left _ _) le_rfl
  have hsube : Ioo (max d e) b ⊆ Ioo e b := Ioo_subset_Ioo (le_max_right _ _) le_rfl
  let s := (c + b) / 2
  have hs : s ∈ Ioo c b := ⟨by dsimp only [s]; linarith, by dsimp only [s]; linarith⟩
  apply continuationCurve_eqOn_of_germ F hM04 T isOpen_Ioo isPreconnected_Ioo
    (fun r hr ↦ htime r ⟨hd.trans_lt ((le_max_left d e).trans_lt hr.1), hr.2⟩)
    (hα.mono hsubd) (hβ.mono hsube)
    (show s ∈ Ioo (max d e) b from ⟨(max_lt hdc hec).trans hs.1, hs.2⟩)
  exact eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
    (fun r hr ↦ (hαγ hr).trans (hβγ hr).symm)

set_option maxHeartbeats 1400000 in
theorem exists_continuation_envelope {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a₀ c b : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₀c : a₀ < c) (hcb : c < b)
    (htime : ∀ s ∈ Ioo 0 b, T - s ^ 2 ∈ J) (α₀ : ℝ → M)
    (hα₀ : IsContinuationCurve F T α₀ (Ioo a₀ b)) :
    ∃ a : ℝ, 0 ≤ a ∧ a < c ∧ ∃ α : ℝ → M,
      IsContinuationCurve F T α (Ioo a b) ∧ EqOn α α₀ (Ioo c b) ∧
      ∀ d : ℝ, 0 ≤ d → d < c → ∀ β : ℝ → M,
        IsContinuationCurve F T β (Ioo d b) → EqOn β α₀ (Ioo c b) → a ≤ d := by
  classical
  let S : Set ℝ := {d | 0 ≤ d ∧ d < c ∧ ∃ β : ℝ → M,
    IsContinuationCurve F T β (Ioo d b) ∧ EqOn β α₀ (Ioo c b)}
  have hS₀ : a₀ ∈ S := ⟨ha₀, ha₀c, α₀, hα₀, fun _ _ ↦ rfl⟩
  have hSne : S.Nonempty := ⟨a₀, hS₀⟩
  have hSbdd : BddBelow S := ⟨0, fun d hd ↦ hd.1⟩
  let a := sInf S
  have ha : 0 ≤ a := le_csInf hSne (fun d hd ↦ hd.1)
  have hac : a < c := (csInf_le hSbdd hS₀).trans_lt ha₀c
  have hex (r : Ioo a b) : ∃ d : ℝ, 0 ≤ d ∧ d < c ∧ ∃ β : ℝ → M,
      IsContinuationCurve F T β (Ioo d b) ∧ EqOn β α₀ (Ioo c b) ∧ d < r := by
    obtain ⟨d, hd, hdr⟩ := exists_lt_of_csInf_lt hSne r.property.1
    obtain ⟨hd0, hdc, β, hβ, hβtail⟩ := hd
    exact ⟨d, hd0, hdc, β, hβ, hβtail, hdr⟩
  choose d hd0 hdc β hβ hβtail hdr using hex
  let α : ℝ → M := fun r ↦ if h : r ∈ Ioo a b then β ⟨r, h⟩ r else α₀ r
  have hnear (r : Ioo a b) : α =ᶠ[𝓝 (r : ℝ)] β r := by
    filter_upwards [isOpen_Ioo.mem_nhds r.property,
      isOpen_Ioo.mem_nhds (show (r : ℝ) ∈ Ioo (d r) b from ⟨hdr r, r.property.2⟩)]
      with t ht htd
    have hcomp := continuationCurve_eqOn_of_tail F hM04 T (hd0 ⟨t, ht⟩) (hd0 r)
      (hdc ⟨t, ht⟩) (hdc r) hcb htime (hβ ⟨t, ht⟩) (hβ r)
      (hβtail ⟨t, ht⟩) (hβtail r)
    change (if h : t ∈ Ioo a b then β ⟨t, h⟩ t else α₀ t) = β r t
    rw [dif_pos ht]
    exact hcomp ⟨max_lt (hdr ⟨t, ht⟩) htd.1, ht.2⟩
  have hα : IsContinuationCurve F T α (Ioo a b) := by
    refine ⟨?_, ?_⟩
    · intro r hr
      have hr' : r ∈ Ioo (d ⟨r, hr⟩) b := ⟨hdr ⟨r, hr⟩, hr.2⟩
      exact ((((hβ ⟨r, hr⟩).smooth r hr').contMDiffAt
        (isOpen_Ioo.mem_nhds hr')).congr_of_eventuallyEq (hnear ⟨r, hr⟩)).contMDiffWithinAt
    · intro r hr x hx
      have hr' : r ∈ Ioo (d ⟨r, hr⟩) b := ⟨hdr ⟨r, hr⟩, hr.2⟩
      have hbase := (hnear ⟨r, hr⟩).self_of_nhds
      have hp := continuationCurvePhase_eventuallyEq F T x (hnear ⟨r, hr⟩)
      have heq := (hβ ⟨r, hr⟩).phase r hr' x (by rwa [← hbase])
      rw [← hp.self_of_nhds] at heq
      exact heq.congr_of_eventuallyEq hp
  refine ⟨a, ha, hac, α, hα, ?_, ?_⟩
  · intro r hr
    have hr' : r ∈ Ioo a b := ⟨hac.trans hr.1, hr.2⟩
    change (if h : r ∈ Ioo a b then β ⟨r, h⟩ r else α₀ r) = α₀ r
    rw [dif_pos hr']
    exact hβtail ⟨r, hr'⟩ hr
  · intro e he hec γ hγ hγtail
    exact csInf_le hSbdd (show e ∈ S from ⟨he, hec, γ, hγ, hγtail⟩)

end PoincareConjecture.M08

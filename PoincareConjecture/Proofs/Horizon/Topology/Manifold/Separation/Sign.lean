import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Function Topology

namespace Poincare.Topology

noncomputable def collarClamp (r t : ℝ) : ℝ := max (-(1 / 2 : ℝ)) (min (1 / 2) (t / r))

theorem continuous_collarClamp (r : ℝ) : Continuous (collarClamp r) :=
  continuous_const.max (continuous_const.min (continuous_id.div_const r))

@[simp] theorem collarClamp_zero (r : ℝ) : collarClamp r 0 = 0 := by
  norm_num [collarClamp]

theorem collarClamp_pos_iff {r t : ℝ} (hr : 0 < r) :
    0 < collarClamp r t ↔ 0 < t := by
  simp [collarClamp, div_pos_iff_of_pos_right hr]

theorem collarClamp_neg_iff {r t : ℝ} (hr : 0 < r) :
    collarClamp r t < 0 ↔ t < 0 := by
  have hdiv : t / r < 0 ↔ t < 0 := by
    rw [div_lt_iff₀ hr, zero_mul]
  simp [collarClamp, hdiv]

theorem collarClamp_eq_zero_iff {r t : ℝ} (hr : 0 < r) :
    collarClamp r t = 0 ↔ t = 0 := by
  unfold collarClamp
  constructor
  · intro h
    have ht : t / r = 0 := by
      rcases le_total (1 / 2 : ℝ) (t / r) with hle | hle
      · rw [min_eq_left hle] at h
        norm_num at h
      · rw [min_eq_right hle] at h
        rcases le_total (-(1 / 2 : ℝ)) (t / r) with hge | hge
        · rwa [max_eq_right hge] at h
        · rw [max_eq_left hge] at h
          norm_num at h
    exact (div_eq_zero_iff.mp ht).resolve_right hr.ne'
  · rintro rfl
    norm_num

private theorem negative_half_eq_half :
    (((-(1 / 2) : ℝ)) : AddCircle (1 : ℝ)) = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  have h := AddCircle.coe_add_period (1 : ℝ) (-(1 / 2 : ℝ))
  norm_num at h ⊢
  exact h.symm

theorem exists_collarSign {Y X : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [ConnectedSpace Y] [TopologicalSpace X] [T2Space X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] (r : ℝ) (hr : 0 < r) {U : Set X}
    (hU : IsOpen U) (e : (Y × Ioo (-r) r) ≃ₜ U) :
    ∃ f : C(X, ℝ),
      (∀ (y : Y) (t : Ioo (-r) r),
        f (e (y, t) : X) = collarClamp r t) ∧
      ∀ x, f x = 0 ↔
        x ∈ range (fun y : Y => (e (y, ⟨0, neg_lt_zero.mpr hr, hr⟩) : X)) := by
  classical
  let t₀ : Ioo (-r) r := ⟨0, neg_lt_zero.mpr hr, hr⟩
  let : T2Space (Y × Ioo (-r) r) := e.symm.t2Space
  let q : Y × Ioo (-r) r → AddCircle (1 : ℝ) :=
    fun z => (collarClamp r z.2 : AddCircle (1 : ℝ)) - ((1 / 2 : ℝ) : AddCircle (1 : ℝ))
  have hq : Continuous q :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_collarClamp r).comp (continuous_subtype_val.comp continuous_snd))).sub
      continuous_const
  have hK : IsCompact ((Subtype.val : Ioo (-r) r → ℝ) ⁻¹' Icc (-r / 2) (r / 2)) := by
    apply IsInducing.subtypeVal.isCompact_preimage' isCompact_Icc
    rintro t ⟨ht₁, ht₂⟩
    exact ⟨⟨t, by constructor <;> linarith⟩, rfl⟩
  have hsupp : HasCompactSupport q := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_univ.prod hK)
    rintro ⟨y, t⟩ ht
    refine ⟨mem_univ _, ?_⟩
    by_contra h
    apply ht
    simp only [mem_preimage, mem_Icc, not_and_or, not_le] at h
    dsimp [q, collarClamp]
    rcases h with h | h
    · have htr : (t : ℝ) / r ≤ -(1 / 2 : ℝ) := by
        apply (div_le_iff₀ hr).mpr
        linarith
      rw [min_eq_right (by linarith : (t : ℝ) / r ≤ (1 / 2 : ℝ)), max_eq_left htr]
      exact sub_eq_zero.mpr negative_half_eq_half
    · have htr : (1 / 2 : ℝ) ≤ (t : ℝ) / r := by
        apply (le_div_iff₀ hr).mpr
        linarith
      rw [min_eq_left htr, max_eq_right (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)]
      exact sub_self _
  let qU : U → AddCircle (1 : ℝ) := q ∘ e.symm
  have hqU : Continuous qU := hq.comp e.symm.continuous
  have hqUsupp : HasCompactSupport qU := hsupp.comp_homeomorph e.symm
  let Q : C(X, AddCircle (1 : ℝ)) :=
    ⟨fun x => Subtype.val.extend qU 0 x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)),
      (HasCompactSupport.continuous_extend_zero hU hqU hqUsupp).add continuous_const⟩
  have hQ (z : Y × Ioo (-r) r) : Q (e z : X) = (collarClamp r z.2 : AddCircle (1 : ℝ)) := by
    dsimp [Q]
    rw [Subtype.val_injective.extend_apply]
    dsimp [qU, q]
    rw [e.symm_apply_apply, sub_add_cancel]
  obtain ⟨y₀⟩ := (inferInstance : Nonempty Y)
  obtain ⟨f, ⟨hf₀, hf⟩, _⟩ := (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
    Q (e (y₀, t₀) : X) 0 (by rw [hQ]; simp [t₀])
  have hformula (z : Y × Ioo (-r) r) : f (e z : X) = collarClamp r z.2 := by
    let : PreconnectedSpace (Ioo (-r) r) := Subtype.preconnectedSpace isPreconnected_Ioo
    apply congr_fun ((AddCircle.isCoveringMap_coe (1 : ℝ)).eq_of_comp_eq
      (f.continuous.comp (continuous_subtype_val.comp e.continuous))
      ((continuous_collarClamp r).comp (continuous_subtype_val.comp continuous_snd))
      (by funext w; exact (congr_fun hf (e w : X)).trans (hQ w))
      (y₀, t₀) (by simpa [t₀] using hf₀)) z
  refine ⟨f, fun y t => hformula (y, t), ?_⟩
  intro x
  constructor
  · intro hzero
    have hxU : x ∈ U := by
      by_contra hxU
      have hQx : Q x = ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
        dsimp [Q]
        rw [Function.extend_apply' _ _ _ (by simpa using hxU)]
        simp
      have hhalf : ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
        rw [← hQx, ← congr_fun hf x]
        change ((f x : ℝ) : AddCircle (1 : ℝ)) = 0
        rw [hzero]
        rfl
      have hh := (AddCircle.coe_eq_zero_iff_of_mem_Ico (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp hhalf
      norm_num at hh
    let z := e.symm ⟨x, hxU⟩
    have hz : f x = collarClamp r z.2 := by simpa [z] using hformula z
    have hzt : z.2 = t₀ := Subtype.ext ((collarClamp_eq_zero_iff hr).mp (hz.symm.trans hzero))
    refine ⟨z.1, ?_⟩
    change (e (z.1, t₀) : X) = x
    rw [← hzt]
    exact congr_arg Subtype.val (e.apply_symm_apply ⟨x, hxU⟩)
  · rintro ⟨y, rfl⟩
    rw [hformula]
    exact collarClamp_zero r

end Poincare.Topology

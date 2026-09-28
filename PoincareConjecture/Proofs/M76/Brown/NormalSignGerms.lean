import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Set Metric SignType

namespace BrownCollar

variable {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q]
  [TopologicalSpace R]

def NormalSignAt (e : OpenPartialHomeomorph (P × ℝ) (Q × ℝ))
    (p : P) (s : SignType) : Prop :=
  s ≠ 0 ∧ ∃ U : Set (P × ℝ), IsOpen U ∧ (p, (0 : ℝ)) ∈ U ∧
    U ⊆ e.source ∧ ∀ z ∈ U, sign (e z).2 = s * sign z.2

namespace NormalSignAt

variable {e : OpenPartialHomeomorph (P × ℝ) (Q × ℝ)} {p : P} {s : SignType}

theorem mem_source (h : NormalSignAt e p s) : (p, (0 : ℝ)) ∈ e.source := by
  obtain ⟨_, U, _, hp, hU, _⟩ := h
  exact hU hp

theorem base_zero (h : NormalSignAt e p s) : (e (p, (0 : ℝ))).2 = 0 := by
  obtain ⟨_, U, _, hp, _, hsign⟩ := h
  apply sign_eq_zero_iff.mp
  simpa only [sign_zero, mul_zero] using hsign (p, 0) hp

theorem exists_open (h : NormalSignAt e p s) :
    ∃ W : Set P, IsOpen W ∧ p ∈ W ∧ ∀ q ∈ W, NormalSignAt e q s := by
  obtain ⟨hs, U, hU, hp, hUs, hsign⟩ := h
  refine ⟨(fun q : P => (q, (0 : ℝ))) ⁻¹' U,
    hU.preimage (continuous_id.prodMk continuous_const), hp, ?_⟩
  intro q hq
  exact ⟨hs, U, hU, hq, hUs, hsign⟩

theorem trans {f : OpenPartialHomeomorph (Q × ℝ) (R × ℝ)} {t : SignType}
    (he : NormalSignAt e p s) (hf : NormalSignAt f (e (p, 0)).1 t) :
    NormalSignAt (e.trans f) p (t * s) := by
  have hbase : ((e (p, (0 : ℝ))).1, (0 : ℝ)) = e (p, 0) := by
    apply Prod.ext
    · rfl
    · exact he.base_zero.symm
  obtain ⟨hs, U, hU, hp, hUs, hsignU⟩ := he
  obtain ⟨ht, V, hV, hq, hVs, hsignV⟩ := hf
  refine ⟨mul_ne_zero ht hs, U ∩ e ⁻¹' V,
    (e.continuousOn.mono hUs).isOpen_inter_preimage hU hV,
    ⟨hp, ?_⟩, ?_, ?_⟩
  · change e (p, 0) ∈ V
    rwa [← hbase]
  · intro z hz
    exact ⟨hUs hz.1, hVs hz.2⟩
  · intro z hz
    change sign (f (e z)).2 = (t * s) * sign z.2
    rw [hsignV (e z) hz.2, hsignU z hz.1, mul_assoc]

theorem symm (h : NormalSignAt e p s) :
    NormalSignAt e.symm (e (p, 0)).1 s := by
  have hbase : ((e (p, (0 : ℝ))).1, (0 : ℝ)) = e (p, 0) := by
    apply Prod.ext
    · rfl
    · exact h.base_zero.symm
  obtain ⟨hs, U, hU, hp, hUs, hsign⟩ := h
  have hsq : s * s = 1 := mul_inv_cancel₀ hs
  refine ⟨hs, e '' U, e.isOpen_image_of_subset_source hU hUs,
    ?_, ?_, ?_⟩
  · rw [hbase]
    exact mem_image_of_mem e hp
  · rintro _ ⟨z, hz, rfl⟩
    exact e.map_source (hUs hz)
  · rintro _ ⟨z, hz, rfl⟩
    rw [e.left_inv (hUs hz), hsign z hz, ← mul_assoc, hsq, one_mul]

end NormalSignAt

theorem normalSignAt_refl (p : P) :
    NormalSignAt (OpenPartialHomeomorph.refl (P × ℝ)) p 1 := by
  refine ⟨one_ne_zero, univ, isOpen_univ, mem_univ _, subset_rfl, ?_⟩
  intro z _
  exact (one_mul (sign z.2)).symm

theorem NormalSignAt.unique {e : OpenPartialHomeomorph (P × ℝ) (Q × ℝ)}
    {p : P} {s t : SignType} (hs : NormalSignAt e p s) (ht : NormalSignAt e p t) :
    s = t := by
  obtain ⟨_, U, hU, hpU, _, hsignU⟩ := hs
  obtain ⟨_, V, hV, hpV, _, hsignV⟩ := ht
  have hopen : IsOpen ((fun a : ℝ => (p, a)) ⁻¹' (U ∩ V)) :=
    (hU.inter hV).preimage (continuous_const.prodMk continuous_id)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨hpU, hpV⟩
  have hr2 : 0 < r / 2 := by positivity
  have hpoint : (p, r / 2) ∈ U ∩ V := by
    apply hball
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr2]
    linarith
  have hs' := hsignU (p, r / 2) hpoint.1
  have ht' := hsignV (p, r / 2) hpoint.2
  rw [sign_pos hr2, mul_one] at hs' ht'
  exact hs'.symm.trans ht'

end BrownCollar

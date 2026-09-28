import PoincareConjecture.Proofs.M64.Mathlib.CappedFirstExitOpen
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order















noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Topology

namespace PoincareConjecture




theorem m64_isClosed_capped_exit_window
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {u : P × ℝ → X} (hu : Continuous u) {U : Set X} (hU : IsOpen U)
    (a b : ℝ) : IsClosed {s : P | ∃ t ∈ Icc a b, u (s, t) ∉ U} := by
  let T := Icc a b
  let : CompactSpace T := isCompact_iff_compactSpace.mp isCompact_Icc
  have hmap : Continuous (fun p : P × T => u (p.1, p.2.val)) :=
    hu.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hC : IsClosed {p : P × T | u (p.1, p.2.val) ∉ U} :=
    hU.isClosed_compl.preimage hmap
  have hprojection := isClosedMap_fst_of_compactSpace _ hC
  convert hprojection using 1
  ext s
  constructor
  · rintro ⟨t, ht, hout⟩
    exact ⟨(s, ⟨t, ht⟩), hout, rfl⟩
  · rintro ⟨⟨s, t⟩, hout, rfl⟩
    exact ⟨t.val, t.property, hout⟩




theorem m64_capped_first_exit_open_measurable
    {P X : Type*} [TopologicalSpace P] [MeasurableSpace P]
    [OpensMeasurableSpace P] [TopologicalSpace X]
    {u : P × ℝ → X} (hu : Continuous u) {U : Set X} (hU : IsOpen U)
    {height : P → ℝ} {R : ℝ}
    (hheight : ∀ s : P, 0 < height s ∧ height s ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) (height s), u (s, t) ∈ U) ∧
      u (s, height s) ∈ closure U ∧
      (height s = R ∨ u (s, height s) ∈ frontier U)) :
    Measurable height := by
  apply measurable_of_Iic
  intro r
  by_cases hRr : R ≤ r
  · have heq : height ⁻¹' Iic r = univ := by
      ext s
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (hheight s).2.1.trans hRr
    rw [heq]
    exact MeasurableSet.univ
  · have hrR : r < R := lt_of_not_ge hRr
    have heq : height ⁻¹' Iic r = ⋃ n : ℕ,
        {s : P | ∃ t ∈ Icc (1 / (n + 1 : ℝ)) r, u (s, t) ∉ U} := by
      ext s
      constructor
      · intro hs
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hheight s).1
        refine mem_iUnion.mpr ⟨n, height s, ⟨hn.le, hs⟩, ?_⟩
        rcases (hheight s).2.2.2.2 with hcap | hfront
        · exact False.elim ((not_lt_of_ge hs) (hcap ▸ hrR))
        · rw [frontier, hU.interior_eq] at hfront
          exact hfront.2
      · intro hs
        obtain ⟨n, t, ht, hout⟩ := mem_iUnion.mp hs
        by_contra hn
        have hrt : r < height s := lt_of_not_ge hn
        have hpos : 0 < t :=
          lt_of_lt_of_le (by positivity : 0 < 1 / (n + 1 : ℝ)) ht.1
        have hinside := (hheight s).2.2.1 t ⟨hpos, ht.2.trans_lt hrt⟩
        exact hout hinside
    rw [heq]
    exact MeasurableSet.iUnion (fun n =>
      (m64_isClosed_capped_exit_window hu hU (1 / (n + 1 : ℝ)) r).measurableSet)




theorem m64_exists_measurable_capped_first_exit_open
    {P X : Type*} [TopologicalSpace P] [MeasurableSpace P]
    [OpensMeasurableSpace P] [TopologicalSpace X]
    {u : P × ℝ → X} (hu : Continuous u) {U : Set X} (hU : IsOpen U)
    {R : ℝ} (hR : 0 < R)
    (henter : ∀ s : P, ∃ eta : ℝ, 0 < eta ∧
      ∀ t ∈ Ioo (0 : ℝ) eta, u (s, t) ∈ U) :
    ∃ height : P → ℝ, Measurable height ∧ ∀ s : P,
      0 < height s ∧ height s ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) (height s), u (s, t) ∈ U) ∧
      u (s, height s) ∈ closure U ∧
      (height s = R ∨ u (s, height s) ∈ frontier U) := by
  have hexists (s : P) : ∃ b : ℝ, 0 < b ∧ b ≤ R ∧
      (∀ t ∈ Ioo (0 : ℝ) b, u (s, t) ∈ U) ∧
      u (s, b) ∈ closure U ∧ (b = R ∨ u (s, b) ∈ frontier U) := by
    obtain ⟨eta, heta, hs⟩ := henter s
    exact m64_exists_capped_first_exit_open
      (hu.comp (continuous_const.prodMk continuous_id)) hU hR heta hs
  choose height hheight using hexists
  refine ⟨height, m64_capped_first_exit_open_measurable hu hU hheight, hheight⟩

end PoincareConjecture

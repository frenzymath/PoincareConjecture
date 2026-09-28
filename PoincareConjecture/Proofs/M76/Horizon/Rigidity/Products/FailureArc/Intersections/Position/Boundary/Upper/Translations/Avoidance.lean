import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineParameterAvoidance

set_option autoImplicit false
open Set Metric AffineSubspace

namespace PoincareConjecture.M76.UpperTranslation
local notation "P2" => (ℝ × ℝ)

theorem planar_line_ne_top (a b : P2) : affineSpan ℝ ({a, b} : Set P2) ≠ ⊤ := by
  intro htop
  have hdim := (collinear_pair ℝ a b).finrank_le_one
  rw [← direction_affineSpan, htop, direction_top, finrank_top,
    Module.finrank_prod, Module.finrank_self] at hdim
  norm_num at hdim

theorem translation_parameter_mem_reflected_line
    {a c d v : P2} (h : a ∈ affineSpan ℝ ({c + v, d + v} : Set P2)) :
    v ∈ affineSpan ℝ ({a - c, a - d} : Set P2) := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  have ht' : AffineMap.lineMap c d t + v = a := by
    exact (show AffineMap.lineMap c d t + v = AffineMap.lineMap (c + v) (d + v) t from
      AffineMap.lineMap_vadd c d v t).trans ht
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨t, ?_⟩
  change AffineMap.lineMap (a -ᵥ c) (a -ᵥ d) t = v
  rw [← AffineMap.vsub_lineMap]
  change a - AffineMap.lineMap c d t = v
  rw [← ht']
  abel

theorem translation_parameter_mem_shifted_line
    {a b c v : P2} (h : c + v ∈ affineSpan ℝ ({a, b} : Set P2)) :
    v ∈ affineSpan ℝ ({a - c, b - c} : Set P2) := by
  obtain ⟨t, ht⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp h
  apply mem_affineSpan_pair_iff_exists_lineMap_eq.mpr
  refine ⟨t, ?_⟩
  change AffineMap.lineMap (a -ᵥ c) (b -ᵥ c) t = v
  rw [← AffineMap.lineMap_vsub]
  change AffineMap.lineMap a b t - c = v
  rw [ht]
  abel

theorem exists_small_translation_avoiding_endpoint_lines
    {I J : Type*} [Finite I] [Finite J]
    (a b : I → P2) (c d : J → P2) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : P2, ‖v‖ < ε ∧ ∀ i j,
      a i ∉ affineSpan ℝ ({c j + v, d j + v} : Set P2) ∧
      b i ∉ affineSpan ℝ ({c j + v, d j + v} : Set P2) ∧
      c j + v ∉ affineSpan ℝ ({a i, b i} : Set P2) ∧
      d j + v ∉ affineSpan ℝ ({a i, b i} : Set P2) := by
  let A : ((I × Bool) × J) ⊕ (I × (J × Bool)) → AffineSubspace ℝ P2
    | Sum.inl ((i, r), j) => affineSpan ℝ
        ({(if r then b i else a i) - c j, (if r then b i else a i) - d j} : Set P2)
    | Sum.inr (i, (j, r)) => affineSpan ℝ
        ({a i - (if r then d j else c j), b i - (if r then d j else c j)} : Set P2)
  have hA : ∀ i, A i ≠ ⊤ := by
    intro i
    cases i <;> exact planar_line_ne_top _ _
  obtain ⟨v, hv, hav⟩ := (AffineSubspace.dense_compl_iUnion A hA).inter_open_nonempty
    (ball 0 ε) isOpen_ball ⟨0, mem_ball_self hε⟩
  have havoid (i) : v ∉ A i := fun h => hav (mem_iUnion.mpr ⟨i, h⟩)
  refine ⟨v, mem_ball_zero_iff.mp hv, fun i j => ?_⟩
  exact ⟨fun h => havoid (Sum.inl ((i, false), j)) (translation_parameter_mem_reflected_line h),
    fun h => havoid (Sum.inl ((i, true), j)) (translation_parameter_mem_reflected_line h),
    fun h => havoid (Sum.inr (i, (j, false))) (translation_parameter_mem_shifted_line h),
    fun h => havoid (Sum.inr (i, (j, true))) (translation_parameter_mem_shifted_line h)⟩

end PoincareConjecture.M76.UpperTranslation

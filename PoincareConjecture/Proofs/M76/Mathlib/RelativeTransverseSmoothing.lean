import PoincareConjecture.Proofs.M76.Mathlib.RelativeSmoothOpenTarget
import PoincareConjecture.Proofs.M76.Mathlib.AffineFrameNormalization










set_option autoImplicit false

open Set ContinuousLinearMap
open scoped Topology ContDiff

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]






theorem Continuous.exists_contDiff_frameTransverse_eqOn
    {f : X → E →L[ℝ] F} (hf : Continuous f) (J : F →L[ℝ] E)
    (hframe : ∀ x, Function.RightInverse J (f x)) (n : ℕ∞)
    {C S U : Set X} (hC : IsCompact C) (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S)
    (hfU : ContDiffOn ℝ n f U) (A : Set E)
    (htrans : ∀ x ∈ C, (f x).ker.IsSecantTransverse A) :
    ∃ g : X → E →L[ℝ] F, ContDiff ℝ n g ∧
      (∀ x, Function.RightInverse J (g x)) ∧ EqOn g f S ∧
      ∀ x ∈ C, (g x).ker.IsSecantTransverse A := by
  let Q0 := f 0
  let T : Set (E →L[ℝ] F) := {Q | (frameNormalize J Q0 Q).ker.IsSecantTransverse A}
  have hT : IsOpen T := isOpen_frameNormalize_transverse J Q0 (hframe 0) A
  have hmem : MapsTo f C T := by
    intro x hx
    change (frameNormalize J Q0 (f x)).ker.IsSecantTransverse A
    rw [frameNormalize_eq_self J Q0 (f x) (hframe x)]
    exact htrans x hx
  obtain ⟨g, hg, heq, _, hgt⟩ := hf.exists_contDiff_eqOn_mem_open n hC hS hU hfU hT hmem
    (ε := 1) zero_lt_one
  refine ⟨fun x => frameNormalize J Q0 (g x),
    (contDiff_frameNormalize J Q0 n).comp hg,
    fun x => rightInverse_frameNormalize J Q0 (hframe 0) (g x), ?_, hgt⟩
  intro x hx
  change frameNormalize J Q0 (g x) = f x
  rw [heq hx, frameNormalize_eq_self J Q0 (f x) (hframe x)]

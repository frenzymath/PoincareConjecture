import PoincareConjecture.Proofs.M76.Mathlib.PLScalarTent
import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCharts

set_option autoImplicit false

open Set Geometry

namespace AddCircle

theorem exists_shortArc_PL_cutoff (p : ℝ) [Fact (0 < p)] {r R : ℝ}
    (_hr : 0 < r) (hrR : r < R) (hRp : R < p / 2) :
    ∃ w : AddCircle p → ℝ,
      Continuous w ∧ (∀ z, w z ∈ Icc 0 1) ∧
      (∀ s : ℝ, |s| ≤ r → w (s : AddCircle p) = 1) ∧
      (∀ z, z ∉ ((↑) : ℝ → AddCircle p) '' Ioo (-R) R → w z = 0) ∧
      ∀ a : ℝ, LocallyPiecewiseAffineOn (w ∘ openPartialHomeomorphCoe p a)
        (openPartialHomeomorphCoe p a).source := by
  classical
  let S := (R + p / 2) / 2
  have hRS : R < S := by dsimp only [S]; linarith
  have hSp : S < p / 2 := by dsimp only [S]; linarith
  let Q := shortArcQuotient p S
  let K : Set ℝ := Icc (-R) R
  let O := (Q '' K)ᶜ
  have hQS : Q.source = Ioo (-S) S := shortArcQuotient_source p hSp
  have hKS : K ⊆ Q.source := by
    rw [hQS]
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hO : IsOpen O :=
    (isCompact_Icc.image_of_continuousOn (Q.continuousOn_toFun.mono hKS)).isClosed.isOpen_compl
  let w : AddCircle p → ℝ := fun z =>
    if z ∈ Q.target then PLScalarTent.value r R (Q.symm z) else 0
  have hwQ : EqOn w (PLScalarTent.value r R ∘ Q.symm) Q.target := by
    intro z hz
    simp only [w, if_pos hz, Function.comp_apply]
  have hwO : EqOn w (fun _ => 0) O := by
    intro z hz
    by_cases hzQ : z ∈ Q.target
    · rw [hwQ hzQ]
      apply PLScalarTent.value_eq_zero hrR
      by_contra hn
      have hs : |Q.symm z| < R := lt_of_not_ge hn
      exact hz ⟨Q.symm z, ⟨(abs_lt.mp hs).1.le, (abs_lt.mp hs).2.le⟩, Q.right_inv hzQ⟩
    · simp only [w, if_neg hzQ]
  have hcover : Q.target ∪ O = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hzQ : z ∈ Q.target
    · exact Or.inl hzQ
    · refine Or.inr ?_
      rintro ⟨s, hs, rfl⟩
      exact hzQ (Q.map_source (hKS hs))
  have hwcontQ : ContinuousOn w Q.target := by
    have h := (PLScalarTent.continuous_value r R).continuousOn.comp
      Q.continuousOn_invFun (fun _ _ => mem_univ _)
    exact h.congr hwQ
  have hwcontO : ContinuousOn w O := continuousOn_const.congr hwO
  have hwcont : Continuous w := by
    apply continuousOn_univ.mp
    rw [← hcover]
    exact hwcontQ.union_of_isOpen hwcontO Q.open_target hO
  refine ⟨w, hwcont, ?_, ?_, ?_, ?_⟩
  · intro z
    by_cases hz : z ∈ Q.target
    · rw [hwQ hz]
      exact PLScalarTent.value_mem_unit r R (Q.symm z)
    · simp only [w, if_neg hz, mem_Icc]
      norm_num
  · intro s hs
    have hsQ : s ∈ Q.source := by
      rw [hQS]
      constructor <;> linarith [(abs_le.mp hs).1, (abs_le.mp hs).2]
    change w (Q s) = 1
    rw [hwQ (Q.map_source hsQ), Function.comp_apply, Q.left_inv hsQ]
    exact PLScalarTent.value_eq_one hrR hs
  · intro z hz
    by_cases hzQ : z ∈ Q.target
    · rw [hwQ hzQ]
      apply PLScalarTent.value_eq_zero hrR
      by_contra hn
      have hs : |Q.symm z| < R := lt_of_not_ge hn
      exact hz ⟨Q.symm z, abs_lt.mp hs, Q.right_inv hzQ⟩
    · simp only [w, if_neg hzQ]
  · intro a
    let A := openPartialHomeomorphCoe p a
    let D := A.trans Q.symm
    have hD := (mem_piecewiseAffineGroupoid_iff ℝ D).mp
      (shortArcQuotient_transition_mem_piecewiseAffineGroupoid p S a) |>.1
    have hinside := ((PLScalarTent.locallyPiecewiseAffineOn_value r R).comp hD).mono
      D.open_source (fun _ hx => ⟨hx, mem_univ _⟩)
    apply LocallyPiecewiseAffineOn.locality
    intro x hx
    by_cases hxQ : A x ∈ Q.target
    · refine ⟨D.source, ⟨hx, hxQ⟩, ?_⟩
      apply (hinside.mono (A.open_source.inter D.open_source) inter_subset_right).congr
      intro y hy
      exact (hwQ hy.2.2).symm
    · have hxO : A x ∈ O := by
        rintro ⟨s, hs, he⟩
        exact hxQ (he ▸ Q.map_source (hKS hs))
      let V := A.source ∩ A ⁻¹' O
      have hV : IsOpen V := A.continuousOn_toFun.isOpen_inter_preimage A.open_source hO
      refine ⟨V, ⟨hx, hxO⟩, ?_⟩
      apply (locallyPiecewiseAffineOn_affine
        (ContinuousAffineMap.const ℝ ℝ (0 : ℝ)) (A.open_source.inter hV)).congr
      intro y hy
      exact (hwO hy.2.2).symm

end AddCircle

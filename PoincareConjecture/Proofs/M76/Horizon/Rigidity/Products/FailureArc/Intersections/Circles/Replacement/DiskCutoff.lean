import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDiskRoof
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_finitePL_disk_cutoff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {d r C : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d r)
    (hC : IsCompact C) (hCd : C ⊆ d \ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : E → ℝ) (Q : Set E), FinitePiecewiseAffineOn w d ∧
      IsCompact Q ∧ Q ⊆ d \ r ∧ C ⊆ Q ∧
      (∀ x ∈ d, 0 ≤ w x ∧ w x ≤ ε) ∧
      (∀ x ∈ C, 0 < w x) ∧ (∀ x ∈ d \ Q, w x = 0) := by
  obtain ⟨roof,hroof,hzero,p,hp,hmax,hbound⟩ := hd.exists_roof
  have hpos (x : E) (hx : x ∈ C) : 0 < roof x := by
    have hx' := hCd hx
    exact lt_of_le_of_ne (hzero x hx'.1).1
      (Ne.symm (fun hz => hx'.2 ((hzero x hx'.1).2.mp hz)))
  obtain ⟨a,ha,hmin⟩ := hC.exists_forall_le'
    (hroof.continuousOn.mono (fun _ hx => (hCd hx).1)) hpos
  let c := min (a / 2) (1 / 6 : ℝ)
  have hc : 0 < c := lt_min (half_pos ha) (by norm_num)
  have hca : c < a := (min_le_left _ _).trans_lt (half_lt_self ha)
  let Q := {x ∈ d | c ≤ roof x}
  have hQ : IsCompact Q := by
    exact hd.isCompact.of_isClosed_subset
      (hroof.continuousOn.preimage_isClosed_of_isClosed hd.isCompact.isClosed isClosed_Ici)
      inter_subset_left
  have hQd : Q ⊆ d \ r := by
    intro x hx
    refine ⟨hx.1,?_⟩
    intro hxr
    have hz := (hzero x hx.1).2.mpr hxr
    have hh := hx.2
    rw [hz] at hh
    exact (not_le_of_gt hc) hh
  have hCQ : C ⊆ Q := fun x hx => ⟨(hCd hx).1,hca.le.trans (hmin x hx)⟩
  let w : E → ℝ := fun x => ε * max 0 (roof x - c)
  let shift : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.id ℝ ℝ - ContinuousAffineMap.const ℝ ℝ c
  have hw : FinitePiecewiseAffineOn w d :=
    ((hroof.postcomp shift).positivePart.postcomp
      (ε • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  refine ⟨w,Q,hw,hQ,hQd,hCQ,?_,?_,?_⟩
  · intro x hx
    have hupper : max 0 (roof x - c) ≤ 1 := by
      apply max_le (by norm_num)
      linarith [(hbound x hx).1]
    exact ⟨mul_nonneg hε.le (le_max_left _ _),
      (mul_le_mul_of_nonneg_left hupper hε.le).trans_eq (mul_one _)⟩
  · intro x hx
    exact mul_pos hε (lt_max_of_lt_right (sub_pos.mpr (hca.trans_le (hmin x hx))))
  · intro x hx
    have hlt : roof x < c := lt_of_not_ge (fun hh => hx.2 ⟨hx.1,hh⟩)
    change ε * max 0 (roof x - c) = 0
    rw [max_eq_left (sub_nonpos.mpr hlt.le),mul_zero]

end PoincareConjecture.M76.Dehn.Annuli

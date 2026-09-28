import PoincareConjecture.Proofs.M76.Mathlib.TriangularCapDisks










set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel




def halfBall (h : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | 0 ≤ h * p.2 ∧ h * p.2 ≤ roof p.1}



def halfBallForms (h : ℝ) : Fin 4 → ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] ℝ :=
  Fin.cases (-(h • (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap)) fun i =>
    h • (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap -
      (coordinates i).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ).toAffineMap



theorem halfBall_eq_halfspaces (h : ℝ) :
    halfBall h = {p | ∀ i, halfBallForms h i p ≤ 0} := by
  ext p
  simp [halfBall, halfBallForms, roof, coordinates, Fin.forall_fin_succ]



theorem halfBallForms_linear_ne_zero {h : ℝ} (hh : h ≠ 0) (i : Fin 4) :
    (halfBallForms h i).linear ≠ 0 := by
  intro hzero
  have hz := LinearMap.congr_fun hzero (((0, 0), 1) : (ℝ × ℝ) × ℝ)
  apply hh
  have hz0 : ((0, 0) : ℝ × ℝ) = 0 := rfl
  cases i using Fin.cases <;> simpa [halfBallForms, hz0] using hz



theorem isClosed_halfBall (h : ℝ) : IsClosed (halfBall h) := by
  rw [halfBall_eq_halfspaces]
  simp only [ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (halfBallForms h i).continuous_of_finiteDimensional
    continuous_const



theorem interior_halfBall {h : ℝ} (hh : h ≠ 0) :
    interior (halfBall h) = {p | 0 < h * p.2 ∧ h * p.2 < roof p.1} := by
  rw [halfBall_eq_halfspaces, interior_finite_affine_halfspaces _
    (halfBallForms_linear_ne_zero hh)]
  ext p
  simp [halfBallForms, roof, coordinates, Fin.forall_fin_succ]



theorem frontier_halfBall {h : ℝ} (hh : h = 1 ∨ h = -1) :
    frontier (halfBall h) = cap h ∪ disk := by
  have hsq : h * h = 1 := by rcases hh with rfl | rfl <;> norm_num
  have hn : h ≠ 0 := by intro hz; simp [hz] at hsq
  rw [frontier, (isClosed_halfBall h).closure_eq, interior_halfBall hn]
  ext p
  change ((0 ≤ h * p.2 ∧ h * p.2 ≤ roof p.1) ∧
    ¬ (0 < h * p.2 ∧ h * p.2 < roof p.1)) ↔ p ∈ cap h ∪ disk
  rw [mem_union, mem_cap, mem_disk]
  constructor
  · rintro ⟨hp, hstrict⟩
    have hb := (roof_nonneg_iff p.1).mp (hp.1.trans hp.2)
    by_cases hz : h * p.2 = 0
    · exact Or.inr ⟨hb, (mul_eq_zero.mp hz).resolve_left hn⟩
    · have hpos : 0 < h * p.2 := lt_of_le_of_ne hp.1 (fun he => hz he.symm)
      have htop : h * p.2 = roof p.1 :=
        le_antisymm hp.2 (not_lt.mp (fun ht => hstrict ⟨hpos, ht⟩))
      left
      refine ⟨hb, ?_⟩
      calc
        p.2 = h * (h * p.2) := by rw [← mul_assoc, hsq, one_mul]
        _ = h * roof p.1 := by rw [htop]
  · rintro (⟨hb, hz⟩ | ⟨hb, hz⟩)
    · have htop : h * p.2 = roof p.1 := by rw [hz, ← mul_assoc, hsq, one_mul]
      exact ⟨⟨htop.symm ▸ (roof_nonneg_iff p.1).mpr hb, htop.le⟩,
        fun hstrict => (ne_of_lt hstrict.2) htop⟩
    · refine ⟨⟨by simp [hz], ?_⟩, ?_⟩
      · simpa [hz] using (roof_nonneg_iff p.1).mpr hb
      · intro hstrict
        simpa [hz] using hstrict.1



theorem isCompact_halfBall {h : ℝ} (hh : h = 1 ∨ h = -1) : IsCompact (halfBall h) := by
  have hc : IsCompact (Icc (((0, 0), -1) : (ℝ × ℝ) × ℝ) ((1, 1), 1)) := isCompact_Icc
  apply hc.of_isClosed_subset (isClosed_halfBall h)
  intro p hp
  change 0 ≤ h * p.2 ∧ h * p.2 ≤ roof p.1 at hp
  have hb := (roof_nonneg_iff p.1).mp (hp.1.trans hp.2)
  rw [base_eq_triangle] at hb
  obtain ⟨hx, hy, hxy⟩ := (TriangleDiskModel.mem_right_region_iff p.1).mp hb
  have hr : roof p.1 ≤ 1 := (roof_le_coordinate p.1 0).trans (by
    change p.1.1 ≤ 1
    linarith)
  have hz : -1 ≤ p.2 ∧ p.2 ≤ 1 := by
    rcases hh with rfl | rfl
    · simp only [one_mul] at hp
      constructor <;> linarith [hp.1, hp.2]
    · simp only [neg_one_mul] at hp
      constructor <;> linarith [hp.1, hp.2]
  exact ⟨⟨⟨hx, hy⟩, hz.1⟩, ⟨⟨by linarith, by linarith⟩, hz.2⟩⟩



theorem interior_halfBall_nonempty {h : ℝ} (hh : h = 1 ∨ h = -1) :
    (interior (halfBall h)).Nonempty := by
  have hsq : h * h = 1 := by rcases hh with rfl | rfl <;> norm_num
  have hn : h ≠ 0 := by intro hz; simp [hz] at hsq
  refine ⟨((1 / 3, 1 / 3), h * (1 / 6)), ?_⟩
  rw [interior_halfBall hn]
  change 0 < h * (h * (1 / 6)) ∧ h * (h * (1 / 6)) < roof (1 / 3, 1 / 3)
  rw [← mul_assoc, hsq, one_mul]
  norm_num [roof]




theorem isFinitePLBallPair_halfBall {h : ℝ} (hh : h = 1 ∨ h = -1) :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (halfBall h) (cap h ∪ disk) := by
  classical
  let H := Finset.univ.image (halfBallForms h)
  have hrep : halfBall h = {p | ∀ A ∈ H, A p ≤ 0} := by
    rw [halfBall_eq_halfspaces]
    ext p
    simp [H]
  have hpair := isFinitePLBallPair_of_affine_halfspaces (isCompact_halfBall hh)
    H hrep (interior_halfBall_nonempty hh)
  rwa [frontier_halfBall hh] at hpair

end TriangularRoofModel

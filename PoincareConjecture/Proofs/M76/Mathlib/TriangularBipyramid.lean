import PoincareConjecture.Proofs.M76.Mathlib.TriangularHalfBalls










set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel



def wholeBall : Set ((ℝ × ℝ) × ℝ) := {p | |p.2| ≤ roof p.1}



def wholeBallForms : (Bool × Fin 3) → ((ℝ × ℝ) × ℝ) →ᵃ[ℝ] ℝ := fun i =>
  (if i.1 then (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
    else -(LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap) -
      (coordinates i.2).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ).toAffineMap

private theorem le_roof_iff (p : ℝ × ℝ) (r : ℝ) :
    r ≤ roof p ↔ ∀ i, r ≤ coordinates i p := by
  simp [roof, coordinates, Fin.forall_fin_succ]

private theorem lt_roof_iff (p : ℝ × ℝ) (r : ℝ) :
    r < roof p ↔ ∀ i, r < coordinates i p := by
  simp [roof, coordinates, Fin.forall_fin_succ]



theorem wholeBall_eq_halfspaces : wholeBall = {p | ∀ i, wholeBallForms i p ≤ 0} := by
  ext p
  change |p.2| ≤ roof p.1 ↔ ∀ i, wholeBallForms i p ≤ 0
  simp only [Prod.forall, Bool.forall_bool]
  change |p.2| ≤ roof p.1 ↔
    (∀ i, -p.2 - coordinates i p.1 ≤ 0) ∧ (∀ i, p.2 - coordinates i p.1 ≤ 0)
  simp only [sub_nonpos, ← le_roof_iff, abs_le]
  constructor <;> rintro ⟨hm, hp⟩ <;> exact ⟨by linarith, hp⟩



theorem wholeBallForms_linear_ne_zero (i : Bool × Fin 3) :
    (wholeBallForms i).linear ≠ 0 := by
  intro hz
  have hv := LinearMap.congr_fun hz (((0, 0), 1) : (ℝ × ℝ) × ℝ)
  rcases i with ⟨b, i⟩
  have hz0 : ((0, 0) : ℝ × ℝ) = 0 := rfl
  cases b <;> simp [wholeBallForms, hz0] at hv



theorem interior_wholeBall : interior wholeBall = {p | |p.2| < roof p.1} := by
  rw [wholeBall_eq_halfspaces, interior_finite_affine_halfspaces _ wholeBallForms_linear_ne_zero]
  ext p
  change (∀ i, wholeBallForms i p < 0) ↔ |p.2| < roof p.1
  simp only [Prod.forall, Bool.forall_bool]
  change ((∀ i, -p.2 - coordinates i p.1 < 0) ∧ (∀ i, p.2 - coordinates i p.1 < 0)) ↔
    |p.2| < roof p.1
  simp only [sub_lt_zero, ← lt_roof_iff, abs_lt]
  constructor <;> rintro ⟨hm, hp⟩ <;> exact ⟨by linarith, hp⟩



theorem wholeBall_eq_union : wholeBall = halfBall 1 ∪ halfBall (-1) := by
  ext p
  change |p.2| ≤ roof p.1 ↔
    (0 ≤ 1 * p.2 ∧ 1 * p.2 ≤ roof p.1) ∨ (0 ≤ -1 * p.2 ∧ -1 * p.2 ≤ roof p.1)
  simp only [one_mul, neg_one_mul]
  constructor
  · intro hp
    by_cases hz : 0 ≤ p.2
    · exact Or.inl ⟨hz, by rwa [abs_of_nonneg hz] at hp⟩
    · have hz' := (not_le.mp hz).le
      exact Or.inr ⟨neg_nonneg.mpr hz', by rwa [abs_of_nonpos hz'] at hp⟩
  · rintro (⟨hz, hp⟩ | ⟨hz, hp⟩)
    · rwa [abs_of_nonneg hz]
    · rwa [abs_of_nonpos (neg_nonneg.mp hz)]



theorem halfBall_inter : halfBall 1 ∩ halfBall (-1) = disk := by
  ext p
  rw [mem_inter_iff, mem_disk]
  change ((0 ≤ 1 * p.2 ∧ 1 * p.2 ≤ roof p.1) ∧
    (0 ≤ -1 * p.2 ∧ -1 * p.2 ≤ roof p.1)) ↔ p.1 ∈ base ∧ p.2 = 0
  simp only [one_mul, neg_one_mul]
  constructor
  · rintro ⟨hp, hq⟩
    exact ⟨(roof_nonneg_iff p.1).mp (hp.1.trans hp.2), by linarith [hp.1, hq.1]⟩
  · rintro ⟨hb, hz⟩
    have hr := (roof_nonneg_iff p.1).mpr hb
    simpa [hz] using And.intro hr hr



theorem isCompact_wholeBall : IsCompact wholeBall := by
  rw [wholeBall_eq_union]
  exact (isCompact_halfBall (Or.inl rfl)).union (isCompact_halfBall (Or.inr rfl))




theorem frontier_wholeBall : frontier wholeBall = cap 1 ∪ cap (-1) := by
  rw [frontier, isCompact_wholeBall.isClosed.closure_eq, interior_wholeBall]
  ext p
  change (|p.2| ≤ roof p.1 ∧ ¬ |p.2| < roof p.1) ↔ p ∈ cap 1 ∪ cap (-1)
  rw [mem_union, mem_cap, mem_cap]
  simp only [one_mul, neg_one_mul]
  constructor
  · rintro ⟨hp, hn⟩
    have heq := le_antisymm hp (not_lt.mp hn)
    have hb := (roof_nonneg_iff p.1).mp ((abs_nonneg p.2).trans hp)
    by_cases hz : 0 ≤ p.2
    · exact Or.inl ⟨hb, by rwa [abs_of_nonneg hz] at heq⟩
    · right
      refine ⟨hb, ?_⟩
      rw [abs_of_nonpos (not_le.mp hz).le] at heq
      linarith
  · rintro (⟨hb, hz⟩ | ⟨hb, hz⟩)
    · have heq : |p.2| = roof p.1 := by
        rw [hz, abs_of_nonneg ((roof_nonneg_iff p.1).mpr hb)]
      exact ⟨heq.le, not_lt.mpr heq.ge⟩
    · have heq : |p.2| = roof p.1 := by
        rw [hz, abs_neg, abs_of_nonneg ((roof_nonneg_iff p.1).mpr hb)]
      exact ⟨heq.le, not_lt.mpr heq.ge⟩



theorem interior_wholeBall_nonempty : (interior wholeBall).Nonempty := by
  refine ⟨((1 / 3, 1 / 3), 0), ?_⟩
  rw [interior_wholeBall]
  norm_num [roof]




theorem isFinitePLBallPair_wholeBall :
    IsFinitePLBallPair ((ℝ × ℝ) × ℝ) wholeBall (cap 1 ∪ cap (-1)) := by
  classical
  let H := Finset.univ.image wholeBallForms
  have hrep : wholeBall = {p | ∀ A ∈ H, A p ≤ 0} := by
    rw [wholeBall_eq_halfspaces]
    ext p
    constructor
    · intro hp A hA
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hA
      exact hp i
    · intro hp i
      exact hp (wholeBallForms i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hpair := isFinitePLBallPair_of_affine_halfspaces isCompact_wholeBall
    H hrep interior_wholeBall_nonempty
  rwa [frontier_wholeBall] at hpair

end TriangularRoofModel

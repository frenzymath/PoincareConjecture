import PoincareConjecture.Proofs.M76.Mathlib.FiniteSegmentCorrespondence
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

open Set Geometry

namespace Set

theorem nat_unit_segments_inter (i j : ℕ) :
    segment ℝ (i : ℝ) (i + 1) ∩ segment ℝ (j : ℝ) (j + 1) ⊆
      convexHull ℝ (({(i : ℝ), (i : ℝ) + 1} : Set ℝ) ∩ {(j : ℝ), (j : ℝ) + 1}) := by
  intro x hx
  have hi : x ∈ Icc (i : ℝ) (i + 1) :=
    (segment_eq_Icc (by linarith : (i : ℝ) ≤ i + 1)) ▸ hx.1
  have hj : x ∈ Icc (j : ℝ) (j + 1) :=
    (segment_eq_Icc (by linarith : (j : ℝ) ≤ j + 1)) ▸ hx.2
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_of_lt hij)
    apply subset_convexHull ℝ _
    exact ⟨Or.inr (by change x = (i : ℝ) + 1; linarith [hi.2, hj.1]),
      Or.inl (by linarith [hi.2, hj.1])⟩
  · simpa only [inter_self, convexHull_pair] using hx.1
  · have h : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_of_lt hji)
    apply subset_convexHull ℝ _
    exact ⟨Or.inl (by linarith [hj.2, hi.1]),
      Or.inr (by change x = (j : ℝ) + 1; linarith [hj.2, hi.1])⟩

theorem iUnion_nat_unit_segments (n : ℕ) :
    (⋃ i : Fin (n + 1), segment ℝ (i.val : ℝ) (i.val + 1)) = Icc 0 (n + 1 : ℝ) := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [segment_eq_Icc (by linarith : (i.val : ℝ) ≤ i.val + 1)] at hi
    have hin : (i.val : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    exact ⟨(Nat.cast_nonneg i.val).trans hi.1, by linarith [hi.2]⟩
  · intro hx
    by_cases htop : x = (n : ℝ) + 1
    · refine ⟨Fin.last n, ?_⟩
      rw [segment_eq_Icc (by simp : ((Fin.last n).val : ℝ) ≤ (Fin.last n).val + 1)]
      simp [htop]
    · have hxn : x < (n + 1 : ℕ) := by push_cast; exact lt_of_le_of_ne hx.2 htop
      let i : Fin (n + 1) := ⟨Nat.floor x, (Nat.floor_lt hx.1).mpr hxn⟩
      refine ⟨i, ?_⟩
      rw [segment_eq_Icc (by linarith : (i.val : ℝ) ≤ i.val + 1)]
      exact ⟨Nat.floor_le hx.1, (Nat.lt_floor_add_one x).le⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

theorem isFinitePLBallPair_linear_chain (p : Fin (n + 2) → E)
    (hp : Function.Injective p)
    (hinter : ∀ i j : Fin (n + 1),
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆
        convexHull ℝ (({p i.castSucc, p i.succ} : Set E) ∩ {p j.castSucc, p j.succ})) :
    IsFinitePLBallPair ℝ (⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ))
      {p 0, p (Fin.last (n + 1))} := by
  have hne (i : Fin (n + 1)) : i.castSucc ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have hcover (v : Fin (n + 2)) :
      ∃ i : Fin (n + 1), v = i.castSucc ∨ v = i.succ := by
    by_cases hv : v.val = 0
    · exact ⟨0, Or.inl (Fin.ext hv)⟩
    · exact ⟨⟨v.val - 1, by omega⟩, Or.inr (Fin.ext (by simp; omega))⟩
  have hrealinj : Function.Injective (fun i : Fin (n + 2) => (i.val : ℝ)) := by
    intro i j h
    exact Fin.ext (Nat.cast_injective h)
  have hrealinter (i j : Fin (n + 1)) :
      segment ℝ (i.castSucc.val : ℝ) i.succ.val ∩
        segment ℝ (j.castSucc.val : ℝ) j.succ.val ⊆
          convexHull ℝ (({(i.castSucc.val : ℝ), (i.succ.val : ℝ)} : Set ℝ) ∩
            {(j.castSucc.val : ℝ), (j.succ.val : ℝ)}) := by
    simpa only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
      nat_unit_segments_inter i.val j.val
  have hsource : (⋃ i : Fin (n + 1), segment ℝ (i.castSucc.val : ℝ) (i.succ.val : ℝ)) =
      Icc 0 (n + 1 : ℝ) := by
    simpa only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one] using
      iUnion_nat_unit_segments n
  have hex := SimplicialComplex.exists_finitePL_segment_correspondence
    (fun i : Fin (n + 1) => i.castSucc) (fun i => i.succ) hne hcover
    (fun i : Fin (n + 2) => (i.val : ℝ)) p hrealinj hp hrealinter hinter
  rw [hsource] at hex
  obtain ⟨f, e, he, hfv, hef⟩ := hex
  obtain ⟨g, hg, heg⟩ := he
  have hf : FinitePiecewiseAffineOn f (Icc 0 (n + 1 : ℝ)) :=
    hg.congr (fun x hx => (heg ⟨x, hx⟩).symm.trans (hef ⟨x, hx⟩))
  have hfi : InjOn f (Icc 0 (n + 1 : ℝ)) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hef ⟨x, hx⟩).trans (hxy.trans (hef ⟨y, hy⟩).symm))))
  have himage : f '' Icc 0 (n + 1 : ℝ) =
      ⋃ i : Fin (n + 1), segment ℝ (p i.castSucc) (p i.succ) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hef ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).property
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property,
        (hef _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))⟩
  have hf0 : f 0 = p 0 := by simpa using hfv 0
  have hflast : f (n + 1 : ℝ) = p (Fin.last (n + 1)) := by
    simpa only [Fin.val_last, Nat.cast_add, Nat.cast_one] using hfv (Fin.last (n + 1))
  have hn : (0 : ℝ) < n + 1 := by positivity
  simpa only [himage, image_pair, hf0, hflast] using
    (isFinitePLBallPair_Icc hn).image hf hfi

end Set

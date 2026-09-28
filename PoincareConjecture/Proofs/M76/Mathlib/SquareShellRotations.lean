import PoincareConjecture.Proofs.M76.Mathlib.SquareShellSectorTransport











set_option autoImplicit false

open Set Geometry

namespace SquareShell



noncomputable def rotation : Fin 4 → (ℝ × ℝ) →ᴬ[ℝ] (ℝ × ℝ) :=
  let x := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  let y := (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  ![x.prod y, (-y).prod x, (-x).prod (-y), y.prod (-x)]



def rotatedSector (a b : ℝ) : Fin 4 → Set (ℝ × ℝ) :=
  ![sector a b,
    {p | -p.1 ∈ Icc a b ∧ p.2 ∈ Icc p.1 (-p.1)},
    {p | -p.2 ∈ Icc a b ∧ p.1 ∈ Icc p.2 (-p.2)},
    {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc (-p.1) p.1}]



def shell (a b : ℝ) : Set (ℝ × ℝ) := {p | ‖p‖ ∈ Icc a b}



theorem rotation_injective (i : Fin 4) : Function.Injective (rotation i) := by
  fin_cases i <;> intro p q he
  all_goals
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp [rotation] at hx hy
    exact Prod.ext (by linarith) (by linarith)



theorem rotation_smul (i : Fin 4) (r : ℝ) (p : ℝ × ℝ) :
    rotation i (r • p) = r • rotation i p := by
  fin_cases i <;> apply Prod.ext <;> dsimp [rotation] <;> ring



theorem norm_rotation (i : Fin 4) (p : ℝ × ℝ) : ‖rotation i p‖ = ‖p‖ := by
  fin_cases i <;> simp [rotation, Prod.norm_def, Real.norm_eq_abs, max_comm]



theorem norm_of_mem_sector {a b : ℝ} {p : ℝ × ℝ} (hp : p ∈ sector a b) :
    ‖p‖ = p.2 := by
  have hy : 0 ≤ p.2 := by linarith [hp.2.1, hp.2.2]
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hy, max_eq_right (abs_le.mpr hp.2)]



theorem rotation_image (a b : ℝ) (i : Fin 4) :
    rotation i '' sector a b = rotatedSector a b i := by
  fin_cases i
  · change (fun p : ℝ × ℝ => (p.1, p.2)) '' sector a b = sector a b
    exact image_id _
  · ext p
    change p ∈ (fun q : ℝ × ℝ => (-q.2, q.1)) '' sector a b ↔
      -p.1 ∈ Icc a b ∧ p.2 ∈ Icc p.1 (-p.1)
    constructor
    · rintro ⟨q, ⟨hr, hx⟩, rfl⟩
      simpa only [neg_neg] using And.intro hr hx
    · rintro ⟨hr, hx⟩
      refine ⟨(p.2, -p.1), ⟨hr, ?_⟩, Prod.ext (neg_neg _) rfl⟩
      simpa only [neg_neg] using hx
  · ext p
    change p ∈ (fun q : ℝ × ℝ => (-q.1, -q.2)) '' sector a b ↔
      -p.2 ∈ Icc a b ∧ p.1 ∈ Icc p.2 (-p.2)
    constructor
    · rintro ⟨q, ⟨hr, hx⟩, rfl⟩
      refine ⟨by simpa only [neg_neg] using hr, ?_⟩
      constructor <;> linarith [hx.1, hx.2]
    · rintro ⟨hr, hx⟩
      refine ⟨(-p.1, -p.2), ⟨hr, ?_⟩, Prod.ext (neg_neg _) (neg_neg _)⟩
      constructor <;> linarith [hx.1, hx.2]
  · ext p
    change p ∈ (fun q : ℝ × ℝ => (q.2, -q.1)) '' sector a b ↔
      p.1 ∈ Icc a b ∧ p.2 ∈ Icc (-p.1) p.1
    constructor
    · rintro ⟨q, ⟨hr, hx⟩, rfl⟩
      exact ⟨hr, by constructor <;> linarith [hx.1, hx.2]⟩
    · rintro ⟨hr, hx⟩
      exact ⟨(-p.2, p.1), ⟨hr, by constructor <;> linarith [hx.1, hx.2]⟩,
        Prod.ext rfl (neg_neg _)⟩



theorem rotatedSector_subset_shell (a b : ℝ) (i : Fin 4) :
    rotatedSector a b i ⊆ shell a b := by
  rw [← rotation_image]
  rintro _ ⟨p, hp, rfl⟩
  change ‖rotation i p‖ ∈ Icc a b
  rw [norm_rotation, norm_of_mem_sector hp]
  exact hp.1




theorem iUnion_rotatedSector (a b : ℝ) : (⋃ i, rotatedSector a b i) = shell a b := by
  apply Subset.antisymm
  · exact iUnion_subset fun i => rotatedSector_subset_shell a b i
  · intro p hp
    have hn : max |p.1| |p.2| ∈ Icc a b := by
      simpa only [shell, mem_ofPred_eq, Prod.norm_def, Real.norm_eq_abs] using hp
    rcases le_total |p.1| |p.2| with hxy | hyx
    · rw [max_eq_right hxy] at hn
      by_cases hy : 0 ≤ p.2
      · rw [abs_of_nonneg hy] at hn hxy
        exact mem_iUnion.mpr ⟨0, hn, abs_le.mp hxy⟩
      · rw [abs_of_neg (lt_of_not_ge hy)] at hn hxy
        refine mem_iUnion.mpr ⟨2, hn, ?_⟩
        simpa only [mem_Icc, neg_neg] using abs_le.mp hxy
    · rw [max_eq_left hyx] at hn
      by_cases hx : 0 ≤ p.1
      · rw [abs_of_nonneg hx] at hn hyx
        exact mem_iUnion.mpr ⟨3, hn, abs_le.mp hyx⟩
      · rw [abs_of_neg (lt_of_not_ge hx)] at hn hyx
        refine mem_iUnion.mpr ⟨1, hn, ?_⟩
        simpa only [mem_Icc, neg_neg] using abs_le.mp hyx

end SquareShell

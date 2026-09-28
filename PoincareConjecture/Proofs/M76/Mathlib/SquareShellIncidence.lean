import PoincareConjecture.Proofs.M76.Mathlib.SquareShellRotations

set_option autoImplicit false

open Set Geometry

namespace SquareShell

theorem rotation_mem_rotatedSector_iff {a b : ℝ} (ha : 0 < a)
    {p : ℝ × ℝ} (hp : p ∈ sector a b) (i j : Fin 4) :
    rotation i p ∈ rotatedSector a b j ↔
      ![![True, p.1 = -p.2, False, p.1 = p.2],
        ![p.1 = p.2, True, p.1 = -p.2, False],
        ![False, p.1 = p.2, True, p.1 = -p.2],
        ![p.1 = -p.2, False, p.1 = p.2, True]] i j := by
  rcases hp with ⟨⟨hpa, hpb⟩, hpl, hpr⟩
  fin_cases i <;> fin_cases j
  all_goals
    first
    | change (p.2 ∈ Icc a b ∧ p.1 ∈ Icc (-p.2) p.2) ↔ True
    | change (-p.1 ∈ Icc a b ∧ p.2 ∈ Icc p.1 (-p.1)) ↔ p.1 = -p.2
    | change (-p.2 ∈ Icc a b ∧ p.1 ∈ Icc p.2 (-p.2)) ↔ False
    | change (p.1 ∈ Icc a b ∧ p.2 ∈ Icc (-p.1) p.1) ↔ p.1 = p.2
    | change (p.1 ∈ Icc a b ∧ -p.2 ∈ Icc (-p.1) p.1) ↔ p.1 = p.2
    | change (- -p.2 ∈ Icc a b ∧ p.1 ∈ Icc (-p.2) (- -p.2)) ↔ True
    | change (-p.1 ∈ Icc a b ∧ -p.2 ∈ Icc p.1 (-p.1)) ↔ p.1 = -p.2
    | change (-p.2 ∈ Icc a b ∧ p.1 ∈ Icc (- -p.2) (-p.2)) ↔ False
    | change (-p.2 ∈ Icc a b ∧ -p.1 ∈ Icc (- -p.2) (-p.2)) ↔ False
    | change (- -p.1 ∈ Icc a b ∧ -p.2 ∈ Icc (-p.1) (- -p.1)) ↔ p.1 = p.2
    | change (- -p.2 ∈ Icc a b ∧ -p.1 ∈ Icc (-p.2) (- -p.2)) ↔ True
    | change (-p.1 ∈ Icc a b ∧ -p.2 ∈ Icc (- -p.1) (-p.1)) ↔ p.1 = -p.2
    | change (-p.1 ∈ Icc a b ∧ p.2 ∈ Icc (- -p.1) (-p.1)) ↔ p.1 = -p.2
    | change (-p.2 ∈ Icc a b ∧ -p.1 ∈ Icc p.2 (-p.2)) ↔ False
    | change (- -p.1 ∈ Icc a b ∧ p.2 ∈ Icc (-p.1) (- -p.1)) ↔ p.1 = p.2
    | change (p.2 ∈ Icc a b ∧ -p.1 ∈ Icc (-p.2) p.2) ↔ True
  all_goals
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩
      first | trivial | linarith
    · intro h
      first
      | contradiction
      | exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem rotation_mem_transport_iff {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    {p q : ℝ × ℝ} (hp : p ∈ sector a b) (hq : q ∈ sector c d)
    (hleft : p.1 = -p.2 ↔ q.1 = -q.2) (hright : p.1 = p.2 ↔ q.1 = q.2)
    (i j : Fin 4) :
    rotation i p ∈ rotatedSector a b j ↔ rotation i q ∈ rotatedSector c d j := by
  rw [rotation_mem_rotatedSector_iff ha hp, rotation_mem_rotatedSector_iff hc hq]
  rw [propext hleft, propext hright]

theorem rotation_transport_eq {a b : ℝ} (ha : 0 < a)
    (e : sector a b → ℝ × ℝ) (R : ℝ → ℝ)
    (he : ∀ x : sector a b,
      (e x).2 = R (x : ℝ × ℝ).2 ∧
      ((x : ℝ × ℝ).1 = -(x : ℝ × ℝ).2 → (e x).1 = -(e x).2) ∧
      ((x : ℝ × ℝ).1 = (x : ℝ × ℝ).2 → (e x).1 = (e x).2))
    (i j : Fin 4) (x y : sector a b)
    (hxy : rotation i x = rotation j y) : rotation i (e x) = rotation j (e y) := by
  by_cases hij : i = j
  · subst j
    have hval : (x : ℝ × ℝ) = y := rotation_injective i hxy
    exact congrArg (fun z => rotation i (e z)) (Subtype.ext hval)
  have hradius : (x : ℝ × ℝ).2 = (y : ℝ × ℝ).2 := by
    calc
      (x : ℝ × ℝ).2 = ‖rotation i x‖ :=
        ((norm_rotation i x).trans (norm_of_mem_sector x.property)).symm
      _ = ‖rotation j y‖ := congrArg norm hxy
      _ = (y : ℝ × ℝ).2 :=
        (norm_rotation j y).trans (norm_of_mem_sector y.property)
  have hnew : (e x).2 = (e y).2 :=
    (he x).1.trans ((congrArg R hradius).trans (he y).1.symm)
  have hxa : a ≤ (x : ℝ × ℝ).2 := x.property.1.1
  have h₁ := congrArg Prod.fst hxy
  have h₂ := congrArg Prod.snd hxy
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals dsimp [rotation] at h₁ h₂ ⊢
  all_goals
    first
    | (exfalso; linarith)
    | (have hxl : (x : ℝ × ℝ).1 = -(x : ℝ × ℝ).2 := by linarith
       have hyr : (y : ℝ × ℝ).1 = (y : ℝ × ℝ).2 := by linarith
       have hxe := (he x).2.1 hxl
       have hye := (he y).2.2 hyr
       apply Prod.ext <;> dsimp <;> linarith)
    | (have hxr : (x : ℝ × ℝ).1 = (x : ℝ × ℝ).2 := by linarith
       have hyl : (y : ℝ × ℝ).1 = -(y : ℝ × ℝ).2 := by linarith
       have hxe := (he x).2.2 hxr
       have hye := (he y).2.1 hyl
       apply Prod.ext <;> dsimp <;> linarith)

end SquareShell

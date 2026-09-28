import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.AlternateResolutionSources








set_option autoImplicit false

open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.AlternateResolutionSources

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

variable {EA EM EC X : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC]
  {SA : Set EA} {SM : Set EM} {SC : Set EC} {Sstrip : Set P2}
  {pA : I01 → EA} {pL pR : I01 → EM} {pC : I01 → EC}
  {pminus pplus : I01 → Sstrip}
  {fA : EA → X} {fL : P2 → X} {fM : EM → X} {fR : P2 → X} {fC : EC → X}
  {g : V2 → X}
  (s : AlternateResolutionSources SA SM SC Sstrip pA pL pR pC pminus pplus
    fA fL fM fR fC g)

theorem A_left_eq_iff (x : SA) (y : Sstrip) :
    s.jA x = s.jL y ↔ ∃! t : I01, (x : EA) = pA t ∧ y = pplus t := by
  have heq : s.jA x = s.jL y ↔ (s.nA x : P2) = s.nL y := by
    constructor
    · intro h
      have h1 := s.H.symm.injective (Subtype.ext h)
      have h2 := (rightDiskCopy_isEmbedding s.mR).injective h1
      have h3 := (rightDiskCopy_isEmbedding s.nAML).injective h2
      exact congrArg Subtype.val ((rightDiskCopy_isEmbedding s.mL).injective h3)
    · intro h
      exact congrArg (fun z : T ↦ (s.H.symm (rightDiskCopy s.mR
        (rightDiskCopy s.nAML (rightDiskCopy s.mL z))) : V2)) (Subtype.ext h)
  exact heq.trans (s.fiberAL x y)

theorem left_middle_eq_iff (x : Sstrip) (y : SM) :
    s.jL x = s.jM y ↔ ∃! t : I01, x = pminus t ∧ (y : EM) = pL t := by
  have heq : s.jL x = s.jM y ↔ (s.mL (leftDiskCopy s.nL x) : P2) = s.nM y := by
    constructor
    · intro h
      have h1 := s.H.symm.injective (Subtype.ext h)
      have h2 := (rightDiskCopy_isEmbedding s.mR).injective h1
      exact congrArg Subtype.val ((rightDiskCopy_isEmbedding s.nAML).injective h2)
    · intro h
      exact congrArg (fun z : T ↦ (s.H.symm (rightDiskCopy s.mR
        (rightDiskCopy s.nAML z)) : V2)) (Subtype.ext h)
  rw [heq, s.fiberM]
  apply existsUnique_congr
  intro t
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨s.nL.injective (Subtype.ext h), hy⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨rfl, hy⟩

theorem middle_right_eq_iff (x : SM) (y : Sstrip) :
    s.jM x = s.jR y ↔ ∃! t : I01, (x : EM) = pR t ∧ y = pminus t := by
  have heq : s.jM x = s.jR y ↔ (s.nAML (leftDiskCopy s.nM x) : P2) = s.nR y := by
    constructor
    · intro h
      have h1 := s.H.symm.injective (Subtype.ext h)
      exact congrArg Subtype.val ((rightDiskCopy_isEmbedding s.mR).injective h1)
    · intro h
      exact congrArg (fun z : T ↦ (s.H.symm (rightDiskCopy s.mR z) : V2)) (Subtype.ext h)
  rw [heq, s.fiberR]
  apply existsUnique_congr
  intro t
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨congrArg Subtype.val (s.nM.injective (Subtype.ext h)), hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨congrArg (fun z : SM ↦ (s.nM z : P2)) (Subtype.ext h), hy⟩

theorem right_C_eq_iff (x : Sstrip) (y : SC) :
    s.jR x = s.jC y ↔ ∃! t : I01, x = pplus t ∧ (y : EC) = pC t := by
  have heq : s.jR x = s.jC y ↔ (s.mR (leftDiskCopy s.nR x) : P2) = s.nC y := by
    constructor
    · intro h
      exact congrArg Subtype.val (s.H.symm.injective (Subtype.ext h))
    · intro h
      exact congrArg (fun z : T ↦ (s.H.symm z : V2)) (Subtype.ext h)
  rw [heq, s.fiberC]
  apply existsUnique_congr
  intro t
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨s.nR.injective (Subtype.ext h), hy⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨rfl, hy⟩

theorem disjoint_A_middle (harms : Disjoint (range pminus) (range pplus)) :
    Disjoint (range s.jA) (range s.jM) := by
  apply disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have h1 := s.H.symm.injective (Subtype.ext hy.symm)
  have h2 := (rightDiskCopy_isEmbedding s.mR).injective h1
  have h3 := congrArg Subtype.val ((rightDiskCopy_isEmbedding s.nAML).injective h2)
  obtain ⟨t, ht, _⟩ := (s.fiberM (rightDiskCopy s.nA x) y).mp h3
  obtain ⟨u, hu, _⟩ := (s.fiberAL x (pminus t)).mp ht.1
  exact disjoint_left.mp harms ⟨t, rfl⟩ ⟨u, hu.2.symm⟩

theorem disjoint_A_C (harms : Disjoint (range pminus) (range pplus)) :
    Disjoint (range s.jA) (range s.jC) := by
  apply disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have h1 := congrArg Subtype.val (s.H.symm.injective (Subtype.ext hy.symm))
  obtain ⟨t, ht, _⟩ := (s.fiberC
    (rightDiskCopy s.nAML (rightDiskCopy s.mL (rightDiskCopy s.nA x))) y).mp h1
  obtain ⟨u, hu, _⟩ := (s.fiberR
    (rightDiskCopy s.mL (rightDiskCopy s.nA x)) (pplus t)).mp ht.1
  exact disjoint_left.mp harms ⟨u, hu.2.symm⟩ ⟨t, rfl⟩

theorem disjoint_middle_C (harms : Disjoint (range pminus) (range pplus)) :
    Disjoint (range s.jM) (range s.jC) := by
  apply disjoint_left.mpr
  rintro z ⟨x, rfl⟩ ⟨y, hy⟩
  have h1 := congrArg Subtype.val (s.H.symm.injective (Subtype.ext hy.symm))
  obtain ⟨t, ht, _⟩ := (s.fiberC (rightDiskCopy s.nAML (leftDiskCopy s.nM x)) y).mp h1
  obtain ⟨u, hu, _⟩ := (s.fiberR (leftDiskCopy s.nM x) (pplus t)).mp ht.1
  exact disjoint_left.mp harms ⟨u, hu.2.symm⟩ ⟨t, rfl⟩

end PoincareConjecture.M76.Dehn.AlternateResolutionSources

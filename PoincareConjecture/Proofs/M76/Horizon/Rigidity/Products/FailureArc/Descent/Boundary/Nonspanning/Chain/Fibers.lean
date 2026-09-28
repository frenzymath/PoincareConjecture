import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Copies

set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.NonspanningChainGeometry

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Strip" => PolygonalCrossingResolution.source

variable {SA SM SC : Set P2} {pA pL pR pC : I01 → P2}
  (s : NonspanningChainGeometry SA SM SC pA pL pR pC)

theorem A_left_eq_iff (x : SA) (y : Strip) :
    s.copyA x = s.copyL y ↔
      ∃ t : I01, (x : P2) = pA t ∧ (y : P2) = ((t : ℝ), 1) := by
  have heq : s.copyA x = s.copyL y ↔ (s.nA x : P2) = s.nL y := by
    constructor
    · intro h
      have h1 := (rightDiskCopy_isEmbedding s.mR).injective h
      have h2 := (rightDiskCopy_isEmbedding s.nAML).injective h1
      exact congrArg Subtype.val ((rightDiskCopy_isEmbedding s.mL).injective h2)
    · intro h
      exact congrArg (fun z : T => rightDiskCopy s.mR
        (rightDiskCopy s.nAML (rightDiskCopy s.mL z))) (Subtype.ext h)
  exact heq.trans (s.fiberAL x y)

theorem left_middle_eq_iff (x : Strip) (y : SM) :
    s.copyL x = s.copyM y ↔
      ∃ t : I01, (x : P2) = ((t : ℝ), -1) ∧ (y : P2) = pL t := by
  have heq : s.copyL x = s.copyM y ↔
      (s.mL (leftDiskCopy s.nL x) : P2) = s.nM y := by
    constructor
    · intro h
      exact congrArg Subtype.val ((rightDiskCopy_isEmbedding s.nAML).injective
        ((rightDiskCopy_isEmbedding s.mR).injective h))
    · intro h
      exact congrArg (fun z : T => rightDiskCopy s.mR (rightDiskCopy s.nAML z))
        (Subtype.ext h)
  rw [heq, s.fiberM]
  apply exists_congr
  intro t
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨congrArg Subtype.val (s.nL.injective (Subtype.ext h)), hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨congrArg (fun z : Strip => (s.nL z : P2)) (Subtype.ext h), hy⟩

theorem middle_right_eq_iff (x : SM) (y : Strip) :
    s.copyM x = s.copyR y ↔
      ∃ t : I01, (x : P2) = pR t ∧ (y : P2) = ((t : ℝ), -1) := by
  have heq : s.copyM x = s.copyR y ↔
      (s.nAML (leftDiskCopy s.nM x) : P2) = s.nR y := by
    constructor
    · exact fun h => congrArg Subtype.val ((rightDiskCopy_isEmbedding s.mR).injective h)
    · exact fun h => congrArg (rightDiskCopy s.mR) (Subtype.ext h)
  rw [heq, s.fiberR]
  apply exists_congr
  intro t
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨congrArg Subtype.val (s.nM.injective (Subtype.ext h)), hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨congrArg (fun z : SM => (s.nM z : P2)) (Subtype.ext h), hy⟩

theorem right_C_eq_iff (x : Strip) (y : SC) :
    s.copyR x = s.copyC y ↔
      ∃ t : I01, (x : P2) = ((t : ℝ), 1) ∧ (y : P2) = pC t := by
  have heq : s.copyR x = s.copyC y ↔
      (s.mR (leftDiskCopy s.nR x) : P2) = s.nC y := Subtype.ext_iff
  rw [heq, s.fiberC]
  apply exists_congr
  intro t
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨congrArg Subtype.val (s.nR.injective (Subtype.ext h)), hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨congrArg (fun z : Strip => (s.nR z : P2)) (Subtype.ext h), hy⟩

theorem A_ne_middle (x : SA) (y : SM) : s.copyA x ≠ s.copyM y := by
  intro h
  have h1 := (rightDiskCopy_isEmbedding s.mR).injective h
  have h2 := congrArg Subtype.val ((rightDiskCopy_isEmbedding s.nAML).injective h1)
  obtain ⟨t, ht, _⟩ := (s.fiberM (rightDiskCopy s.nA x) y).mp h2
  obtain ⟨u, _, hu⟩ := (s.fiberAL x ⟨((t : ℝ), -1), t.property, by norm_num⟩).mp ht
  have hv := congrArg Prod.snd hu
  norm_num at hv

theorem A_ne_right (x : SA) (y : Strip) : s.copyA x ≠ s.copyR y := by
  intro h
  have h1 := congrArg Subtype.val ((rightDiskCopy_isEmbedding s.mR).injective h)
  obtain ⟨t, ht, _⟩ := (s.fiberR (rightDiskCopy s.mL (rightDiskCopy s.nA x)) y).mp h1
  apply s.A_ne_middle x ⟨pR t, s.pR_mem t⟩
  exact congrArg (fun z : T => rightDiskCopy s.mR (rightDiskCopy s.nAML z))
    (Subtype.ext ht)

theorem A_ne_C (x : SA) (y : SC) : s.copyA x ≠ s.copyC y := by
  intro h
  obtain ⟨t, ht, _⟩ := (s.fiberC
    (rightDiskCopy s.nAML (rightDiskCopy s.mL (rightDiskCopy s.nA x))) y).mp
      (congrArg Subtype.val h)
  obtain ⟨u, _, hu⟩ := (s.fiberR (rightDiskCopy s.mL (rightDiskCopy s.nA x))
    ⟨((t : ℝ), 1), t.property, by norm_num⟩).mp ht
  have hv := congrArg Prod.snd hu
  norm_num at hv

theorem left_ne_C (x : Strip) (y : SC) : s.copyL x ≠ s.copyC y := by
  intro h
  obtain ⟨t, ht, _⟩ := (s.fiberC
    (rightDiskCopy s.nAML (rightDiskCopy s.mL (leftDiskCopy s.nL x))) y).mp
      (congrArg Subtype.val h)
  obtain ⟨u, _, hu⟩ := (s.fiberR (rightDiskCopy s.mL (leftDiskCopy s.nL x))
    ⟨((t : ℝ), 1), t.property, by norm_num⟩).mp ht
  have hv := congrArg Prod.snd hu
  norm_num at hv

theorem middle_ne_C (x : SM) (y : SC) : s.copyM x ≠ s.copyC y := by
  intro h
  obtain ⟨t, ht, _⟩ := (s.fiberC (rightDiskCopy s.nAML (leftDiskCopy s.nM x)) y).mp
    (congrArg Subtype.val h)
  obtain ⟨u, _, hu⟩ := (s.fiberR (leftDiskCopy s.nM x)
    ⟨((t : ℝ), 1), t.property, by norm_num⟩).mp ht
  have hv := congrArg Prod.snd hu
  norm_num at hv

theorem left_ne_right (hdisj : Disjoint (range pL) (range pR))
    (x y : Strip) : s.copyL x ≠ s.copyR y := by
  intro h
  have h1 := congrArg Subtype.val ((rightDiskCopy_isEmbedding s.mR).injective h)
  obtain ⟨t, ht, _⟩ := (s.fiberR (rightDiskCopy s.mL (leftDiskCopy s.nL x)) y).mp h1
  obtain ⟨u, _, hu⟩ := (s.fiberM (leftDiskCopy s.nL x) ⟨pR t, s.pR_mem t⟩).mp ht
  exact disjoint_left.mp hdisj ⟨u, hu.symm⟩ ⟨t, rfl⟩

end PoincareConjecture.M76.Dehn.NonspanningChainGeometry

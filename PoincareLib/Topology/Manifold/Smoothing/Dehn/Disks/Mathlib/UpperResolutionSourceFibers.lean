import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.UpperResolutionSources

/-!
# All pairwise source fibers of the normalized upper resolution

The actual normalized copies identify only the two prescribed whole arms.
The two old exterior disks stay disjoint. These statements concern source
points of the same normalized map, before its target double curves are counted.
-/

set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel

namespace PoincareMT.M76.Dehn.UpperResolutionSources

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "I01" => Icc (0 : ℝ) 1

variable {EA EC X : Type*}
  [NormedAddCommGroup EA] [NormedSpace ℝ EA]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC]
  {SA : Set EA} {SC : Set EC} {Sstrip : Set P2}
  {pA : I01 → EA} {pC : I01 → EC} {pminus pplus : I01 → Sstrip}
  {fA : EA → X} {fS : P2 → X} {fC : EC → X} {g : V2 → X}
  (s : UpperResolutionSources SA SC Sstrip pA pC pminus pplus fA fS fC g)

/-- The first attaching fiber survives the whole second attachment and normalization. -/
theorem left_middle_eq_iff (x : SA) (y : Sstrip) :
    s.jA x = s.jS y ↔ ∃! t : I01, (x : EA) = pA t ∧ y = pminus t := by
  have heq : s.jA x = s.jS y ↔ (s.nA x : P2) = s.nS y := by
    constructor
    · intro h
      have h1 := s.H.symm.injective (Subtype.ext h)
      have h2 := (rightDiskCopy_isEmbedding s.m).injective h1
      exact congrArg Subtype.val h2
    · intro h
      have h1 : rightDiskCopy s.nA x = leftDiskCopy s.nS y := Subtype.ext h
      exact congrArg (fun z ↦ (s.H.symm (rightDiskCopy s.m z) : V2)) h1
  exact heq.trans (s.fiberAS x y)

/-- The second attaching fiber identifies exactly the complete opposite arm. -/
theorem middle_right_eq_iff (y : Sstrip) (z : SC) :
    s.jS y = s.jC z ↔ ∃! t : I01, y = pplus t ∧ (z : EC) = pC t := by
  have heq : s.jS y = s.jC z ↔
      (s.m (leftDiskCopy s.nS y) : P2) = s.nC z := by
    constructor
    · intro h
      exact congrArg Subtype.val (s.H.symm.injective (Subtype.ext h))
    · intro h
      exact congrArg (fun z ↦ (s.H.symm z : V2)) (Subtype.ext h)
  rw [heq, s.fiberC]
  apply existsUnique_congr
  intro t
  constructor
  · rintro ⟨h, hz⟩
    exact ⟨s.nS.injective (Subtype.ext h), hz⟩
  · rintro ⟨rfl, hz⟩
    exact ⟨rfl, hz⟩

/-- Distinct strip arms prevent an identification of the two old exterior copies. -/
theorem disjoint_outer (harms : Disjoint (range pminus) (range pplus)) :
    Disjoint (range s.jA) (range s.jC) := by
  apply Set.disjoint_left.mpr
  rintro w ⟨x, rfl⟩ ⟨z, hz⟩
  have houter : (s.m (rightDiskCopy s.nA x) : P2) = s.nC z :=
    congrArg Subtype.val (s.H.symm.injective (Subtype.ext hz.symm))
  obtain ⟨t, ht, _⟩ := (s.fiberC (rightDiskCopy s.nA x) z).mp houter
  obtain ⟨u, hu, _⟩ := (s.fiberAS x (pplus t)).mp ht.1
  exact Set.disjoint_left.mp harms ⟨u, hu.2.symm⟩ ⟨t, rfl⟩

end PoincareMT.M76.Dehn.UpperResolutionSources

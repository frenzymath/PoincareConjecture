import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Core.Connected
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.Level.Source
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.RegularLevel.Separation
import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def separatingLatitude : Real := (3 / 5 + upperRoot) / 2

def southernCap : Set S2 := {p | height p < 1 ∧ (p : E3) 2 < separatingLatitude}

def northernCap : Set S2 := {p | height p < 1 ∧ separatingLatitude < (p : E3) 2}

def upperCap : Set S2 := {p | 13 / 10 < height p}

theorem separatingLatitude_bounds : (3 / 5 : Real) < separatingLatitude ∧
    separatingLatitude < upperRoot := by
  dsimp [separatingLatitude]
  constructor <;> linarith [upperRoot_bounds.1]

theorem sublevel_one_latitude {p : S2} (hp : height p ≤ 1) :
    (p : E3) 2 ≤ 3 / 5 ∨ upperRoot ≤ (p : E3) 2 := by
  by_cases hz0 : (p : E3) 2 ≤ 0
  · exact Or.inl (by linarith)
  have hn : ((p : E3) 0)^2+((p : E3) 1)^2+((p : E3) 2)^2=1 := by
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
    exact hn.symm
  have hz1 : (p : E3) 2 ≤ 1 := by
    nlinarith [sq_nonneg ((p : E3) 0), sq_nonneg ((p : E3) 1)]
  have hx : (p : E3) 0 ≤ levelAbscissa ((p : E3) 2) := by
    rw [height_apply] at hp
    dsimp [levelAbscissa]
    nlinarith
  have hL : levelAbscissa ((p : E3) 2) ≤ 0 := by
    dsimp [levelAbscissa]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num) (lt_of_not_ge hz0).le) (by linarith)
  have hr : 0 ≤ levelRadicand ((p : E3) 2) := by
    dsimp [levelRadicand]
    nlinarith [sq_nonneg ((p : E3) 1)]
  exact ((levelRadicand_nonneg_iff _).mp hr).elim (fun h => Or.inl h.2) (fun h => Or.inr h.1)

theorem sublevel_one_ne_separatingLatitude {p : S2} (hp : height p ≤ 1) :
    (p : E3) 2 ≠ separatingLatitude := by
  intro heq
  rcases sublevel_one_latitude hp with h | h
  · linarith [separatingLatitude_bounds.1]
  · linarith [separatingLatitude_bounds.2]

theorem isOpen_southernCap : IsOpen southernCap :=
  (isOpen_lt height_contMDiff.continuous continuous_const).inter
    (isOpen_lt (by fun_prop : Continuous (fun p : S2 => (p : E3) 2)) continuous_const)

theorem isOpen_northernCap : IsOpen northernCap :=
  (isOpen_lt height_contMDiff.continuous continuous_const).inter
    (isOpen_lt continuous_const (by fun_prop : Continuous (fun p : S2 => (p : E3) 2)))

theorem isOpen_upperCap : IsOpen upperCap := isOpen_lt continuous_const height_contMDiff.continuous

theorem retainedBand_compl : retainedBandᶜ = southernCap ∪ northernCap ∪ upperCap := by
  rw [union_assoc]
  ext p
  change ¬(1 ≤ height p ∧ height p ≤ 13 / 10) ↔
    (height p < 1 ∧ (p : E3) 2 < separatingLatitude) ∨
      (height p < 1 ∧ separatingLatitude < (p : E3) 2) ∨ 13 / 10 < height p
  constructor
  · intro hp
    by_cases hh : height p < 1
    · rcases lt_or_gt_of_ne (sublevel_one_ne_separatingLatitude hh.le) with hz | hz
      · exact Or.inl ⟨hh, hz⟩
      · exact Or.inr (Or.inl ⟨hh, hz⟩)
    · exact Or.inr (Or.inr (lt_of_not_ge (fun h => hp ⟨le_of_not_gt hh, h⟩)))
  · rintro (h | h | h) <;> intro hh
    · exact (not_lt_of_ge hh.1) h.1
    · exact (not_lt_of_ge hh.1) h.1
    · exact (not_lt_of_ge hh.2) h

theorem frontier_southernCap_subset : frontier southernCap ⊆ outerSourceCircle := by
  have hcl : closure southernCap ⊆ {p : S2 | height p ≤ 1 ∧ (p : E3) 2 ≤ separatingLatitude} :=
    closure_minimal (fun p hp => ⟨hp.1.le, hp.2.le⟩)
      ((isClosed_le height_contMDiff.continuous continuous_const).inter
        (isClosed_le (by fun_prop : Continuous (fun p : S2 => (p : E3) 2)) continuous_const))
  intro p hp
  have hpcl := hcl hp.1
  have hpout : p ∉ southernCap := by
    simpa only [isOpen_southernCap.interior_eq] using hp.2
  have hz : (p : E3) 2 < separatingLatitude :=
    lt_of_le_of_ne hpcl.2 (sublevel_one_ne_separatingLatitude hpcl.1)
  have hh : height p=1 := by
    apply le_antisymm hpcl.1
    exact le_of_not_gt (fun h => hpout ⟨h, hz⟩)
  have hm : p ∈ height ⁻¹' {(1 : Real)} := hh
  rw [lower_height_level_eq_sourceCircles] at hm
  rcases hm with hm | hm
  · exact hm
  · have hi := innerSourceCircle_latitude hm
    linarith [hi.1, separatingLatitude_bounds.2]

theorem frontier_northernCap_subset : frontier northernCap ⊆ innerSourceCircle := by
  have hcl : closure northernCap ⊆ {p : S2 | height p ≤ 1 ∧ separatingLatitude ≤ (p : E3) 2} :=
    closure_minimal (fun p hp => ⟨hp.1.le, hp.2.le⟩)
      ((isClosed_le height_contMDiff.continuous continuous_const).inter
        (isClosed_le continuous_const (by fun_prop : Continuous (fun p : S2 => (p : E3) 2))))
  intro p hp
  have hpcl := hcl hp.1
  have hpout : p ∉ northernCap := by
    simpa only [isOpen_northernCap.interior_eq] using hp.2
  have hz : separatingLatitude < (p : E3) 2 :=
    lt_of_le_of_ne hpcl.2 (Ne.symm (sublevel_one_ne_separatingLatitude hpcl.1))
  have hh : height p=1 := by
    apply le_antisymm hpcl.1
    exact le_of_not_gt (fun h => hpout ⟨h, hz⟩)
  have hm : p ∈ height ⁻¹' {(1 : Real)} := hh
  rw [lower_height_level_eq_sourceCircles] at hm
  rcases hm with hm | hm
  · have hi := outerSourceCircle_latitude hm
    linarith [hi.2, separatingLatitude_bounds.1]
  · exact hm

theorem frontier_upperCap_subset : frontier upperCap ⊆ height ⁻¹' {(13 / 10 : Real)} := by
  have hcl : closure upperCap ⊆ {p : S2 | 13 / 10 ≤ height p} :=
    closure_minimal (fun p hp => (show 13 / 10 < height p from hp).le)
      (isClosed_le continuous_const height_contMDiff.continuous)
  intro p hp
  have hpout : p ∉ upperCap := by simpa only [isOpen_upperCap.interior_eq] using hp.2
  exact le_antisymm (le_of_not_gt hpout) (hcl hp.1)

end Poincare.Manifold.Schoenflies.Saddle.Nested

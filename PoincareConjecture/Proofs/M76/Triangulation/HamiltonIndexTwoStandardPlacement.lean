import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoStandardSource
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexTwoPlacement
import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinder









set_option autoImplicit false

open Set Metric Geometry CoordinateHalfBoxes

namespace PoincareConjecture.M76.HamiltonIndexTwoStandard

local notation "V" => (Fin 3 → ℝ)

private theorem box_subset_closedBall :
    Icc lowerBound upperBound ⊆ closedBall (0 : V) 2 := by
  have hlo (i : Fin 3) : (-2 : ℝ) ≤ lowerBound i := by
    fin_cases i <;> norm_num [lowerBound]
  have hhi (i : Fin 3) : upperBound i ≤ (2 : ℝ) := by
    fin_cases i <;> norm_num [upperBound]
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  intro i
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨(hlo i).trans (hx.1 i), (hx.2 i).trans (hhi i)⟩

private theorem box_subset_cylinder :
    Icc lowerBound upperBound ⊆ coordinateCylinder ({0, 1} : Finset (Fin 3)) := by
  intro x hx i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact abs_le.mpr ⟨hx.1 0, hx.2 0⟩
  · exact abs_le.mpr ⟨hx.1 1, hx.2 1⟩

private theorem unit_box_image :
    coordinates '' prism (-1) 1 = closedBall (0 : V) 1 := by
  ext x
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [Real.norm_eq_abs]
  constructor
  · rintro ⟨p, hp, rfl⟩ i
    fin_cases i
    · exact abs_le.mpr hp.1.1
    · exact abs_le.mpr hp.1.2
    · exact abs_le.mpr hp.2
  · intro hx
    refine ⟨((x 0, x 1), x 2), ⟨⟨abs_le.mp (hx 0), abs_le.mp (hx 1)⟩,
      abs_le.mp (hx 2)⟩, ?_⟩
    ext i
    fin_cases i <;> rfl





theorem exists_supported_placement
    (T : HamiltonIndexTwoMarkedBall frame)
    (e : ∀ j, source.disk j ≃ₜ T.disk j) (he : ∀ j, (e j).IsFinitePL)
    (hfix : ∀ j (x : source.disk j), (x : V) ∈ frame.rim j → (e j x : V) = x) :
    ∃ Q : V ≃ₜ V,
      FinitePiecewiseAffineOn (Q : V → V) (closedBall (0 : V) 1) ∧
      (∀ x : V, 2 ≤ ‖x‖ → Q x = x) ∧
      EqOn Q id ((coordinateCylinder ({0, 1} : Finset (Fin 3)))ᶜ ∪
        frontier (coordinateCylinder ({0, 1} : Finset (Fin 3)))) ∧
      Q '' source.carrier = T.carrier ∧
      MapsTo Q (closedBall (0 : V) 1) T.carrier := by
  obtain ⟨Q, hQ, hQimage, hQfix⟩ :=
    exists_hamilton_indexTwo_relative_placement (by simp) frame source T e he hfix
  have hcoreL : closedBall (0 : V) 1 ⊆ Icc frame.lower frame.upper :=
    unit_core_subset_source.trans source.subset_box
  have hcorePair := (prism_ballPair (by norm_num : (-1 : ℝ) < 1)).affine_image
    coordinates.toContinuousAffineMap coordinates.injective.injOn
  change IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (coordinates '' prism (-1) 1)
    (coordinates '' ((band (-1) 1 ∪ endDisk (-1)) ∪ endDisk 1)) at hcorePair
  rw [unit_box_image] at hcorePair
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hcorePair
  refine ⟨Q, ?_, ?_, ?_, hQimage, ?_⟩
  · rw [← hKs]
    exact hQ.restrict K hK (hKs.subset.trans hcoreL)
  · intro x hx
    apply hQfix
    intro hxi
    have hball := interior_mono box_subset_closedBall hxi
    rw [interior_closedBall (0 : V) (by norm_num : (2 : ℝ) ≠ 0)] at hball
    exact (not_lt_of_ge hx) (mem_ball_zero_iff.mp hball)
  · intro x hx
    apply hQfix
    intro hxi
    have hc := interior_mono box_subset_cylinder hxi
    rcases hx with hx | hx
    · exact hx (interior_subset hc)
    · exact hx.2 hc
  · intro x hx
    exact hQimage.subset (mem_image_of_mem Q (unit_core_subset_source hx))

end PoincareConjecture.M76.HamiltonIndexTwoStandard

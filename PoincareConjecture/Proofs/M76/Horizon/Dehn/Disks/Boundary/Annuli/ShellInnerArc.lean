import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoIntervalDiskNormalization
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCircleArcs
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval









set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

theorem exists_proper_interval_between_boundary_points
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S Q : Set E} (hS : IsFinitePLBallPair (ℝ × ℝ) S Q)
    {a b : E} (ha : a ∈ Q) (hb : b ∈ Q) (hab : a ≠ b) :
    ∃ W : Set E, IsFinitePLBallPair ℝ W {a, b} ∧
      W ⊆ S ∧ W ∩ Q = {a, b} ∧ W \ {a, b} ⊆ S \ Q := by
  obtain ⟨U, V, hU, hV, hUV, hIV⟩ := hS.exists_boundary_arcs ha hb hab
  obtain ⟨p, hp, hp0, hp1⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨q, hq, hq0, hq1⟩ := hV.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨H, d, _hH, hd, hdi, hdS, _hdH, hdrim, hd0, _hd1, _⟩ :=
    exists_two_interval_disk_normalization (hUV.symm ▸ hS) hab hIV p q hp hq hp0 hp1 hq0 hq1
  let A : ℝ →L[ℝ] V2 := ContinuousLinearMap.pi (fun _ ↦ ContinuousLinearMap.id ℝ ℝ)
  have hAval (t : ℝ) : A t = fun _ ↦ t := rfl
  have hnorm (t : ℝ) : ‖A t‖ = |t| := by simp [hAval]
  have hAinj : Function.Injective A := by
    intro s t h
    exact congrFun h 0
  have hAD : A '' Icc (-1 : ℝ) 1 ⊆ D2 := by
    rintro z ⟨t, ht, rfl⟩
    rw [mem_closedBall_zero_iff, hnorm, abs_le]
    exact ht
  have hball := (isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)).affine_image
    A.toContinuousAffineMap hAinj.injOn
  have hdInj : InjOn d D2 := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hdi.injective (show
      (fun z : D2 ↦ d z) ⟨x, hx⟩ = (fun z : D2 ↦ d z) ⟨y, hy⟩ from hxy))
  have hAm : A (-1) = (squareRimBase : V2) := by
    ext j
    fin_cases j <;> rfl
  have hAp : A 1 = (squareRimVertex 2 : V2) := by
    ext j
    fin_cases j <;> rfl
  have hdm : d (A (-1)) = a := by
    have h := (hd0 (0 : unitInterval)).trans hp0
    change d (squareRimHalf false 0) = a at h
    simpa only [squareRimHalf_zero, hAm] using h
  have hdp : d (A 1) = b := by
    have h := (hd0 (1 : unitInterval)).trans hp1
    change d (squareRimHalf false 1) = b at h
    simpa only [squareRimHalf_one, hAp] using h
  have hW : IsFinitePLBallPair ℝ (d '' (A '' Icc (-1 : ℝ) 1)) {a, b} := by
    have h := hball.image_of_subset hd hAD hdInj
    change IsFinitePLBallPair ℝ (d '' (A '' Icc (-1 : ℝ) 1)) (d '' (A '' {-1, 1})) at h
    simpa only [image_pair, hdm, hdp] using h
  have hWS : d '' (A '' Icc (-1 : ℝ) 1) ⊆ S := image_mono hAD |>.trans hdS.subset
  have hproper : d '' (A '' Icc (-1 : ℝ) 1) \ {a, b} ⊆ S \ Q := by
    rintro w ⟨⟨z, ⟨t, ht, rfl⟩, rfl⟩, hnot⟩
    refine ⟨hWS ⟨A t, ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
    intro hq'
    have hh := (hdrim ⟨A t, hAD ⟨t, ht, rfl⟩⟩).mp (hUV.symm ▸ hq')
    rw [mem_sphere_zero_iff_norm, hnorm, abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at hh
    rcases hh with hh | hh
    · exact hnot (Or.inr (hh ▸ hdp))
    · exact hnot (Or.inl (hh ▸ hdm))
  refine ⟨_, hW, hWS, ?_, hproper⟩
  apply Subset.antisymm
  · intro w hw
    by_contra hnot
    exact (hproper ⟨hw.1, hnot⟩).2 hw.2
  · intro w hw
    exact ⟨hW.1 hw, by rcases hw with rfl | rfl <;> assumption⟩

end PoincareConjecture.M76.Dehn

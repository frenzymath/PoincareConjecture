import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereFirstCap
import PoincareConjecture.Proofs.M76.Mathlib.CompactZeroFiberBand

set_option autoImplicit false

open Set

namespace Homeomorph

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsFinitePL.exists_local_first_height_cap_ball
    {s : Set E} {C : Set F} {e : s ≃ₜ frontier C} (he : e.IsFinitePL)
    (hC : IsCompact C) (hcv : Convex ℝ C) (hne : (interior C).Nonempty)
    (hdimF : Module.finrank ℝ F = 3) (hdimE : Module.finrank ℝ E = 3)
    {p : E} (hp : p ∈ s) (A : E →ᵃ[ℝ] ℝ) (hpA : A p = 0)
    (hmin : ∀ x ∈ s, 0 ≤ A x) (hzero : s ∩ {x | A x = 0} = {p})
    {U : Set E} (hU : IsOpen U) (hUcv : Convex ℝ U) (hpU : p ∈ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ β ∈ Ioo (0 : ℝ) ε, ∃ d : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d (s ∩ {x | A x = β}) ∧
      (∀ x ∈ d, A x = β) ∧ d ∩ s = s ∩ {x | A x = β} ∧
      IsFinitePLBallPair ((ℝ × ℝ) × ℝ) (convexJoin ℝ {p} d)
        (d ∪ (s ∩ {x | A x ≤ β})) ∧
      convexJoin ℝ {p} d ∩ s = s ∩ {x | A x ≤ β} ∧
      convexJoin ℝ {p} d ⊆ {x | A x ∈ Icc 0 β} ∧
      d ⊆ U ∧ convexJoin ℝ {p} d ⊆ U := by
  have hs : IsCompact s := by
    obtain ⟨f, hf, _⟩ := he
    exact hf.isCompact
  obtain ⟨η, hη, hηU⟩ := hs.exists_pos_abs_le_subset_of_zero_fiber hU
    A.continuous_of_finiteDimensional.continuousOn
    (hzero.subset.trans (singleton_subset_iff.mpr hpU))
  obtain ⟨β, hβ, d, hd, hdplane, hdcontact, hball, hcontact, hheight, _⟩ :=
    he.exists_first_height_cap_ball hC hcv hne hdimF hdimE hp A hpA hmin hzero
      (lt_min hη hε)
  have hrimU : s ∩ {x | A x = β} ⊆ U := by
    intro x hx
    apply hηU x hx.1
    rw [hx.2, abs_of_pos hβ.1]
    exact (hβ.2.trans_le (min_le_left _ _)).le
  obtain ⟨n, P, hPi, hPe, hPb⟩ := hd.exists_polygon_boundary
  let B := A - AffineMap.const ℝ E β
  have hBplane : d ⊆ {x | B x = 0} := by
    intro x hx
    change A x - β = 0
    rw [hdplane x hx, sub_self]
  have hAlinear : A.linear ≠ 0 := by
    intro hz
    have hPheight : A (P 0) = β := (hPb.subset (P.vertex_mem_boundary 0)).2
    have h := A.linearMap_vsub (P 0) p
    change A.linear (P 0 - p) = A (P 0) - A p at h
    rw [hz, LinearMap.zero_apply, hPheight, hpA, sub_zero] at h
    exact hβ.1.ne h
  have hBlinear : B.linear ≠ 0 := by simpa [B] using hAlinear
  have hdP : IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ) := by rwa [hPb]
  have hdU : d ⊆ U := hdP.subset_convex_of_planar_polygon_boundary P hPe hPi B
    hBlinear hdimE hBplane hUcv (by
      rintro x ⟨i, rfl⟩
      exact hrimU (hPb.subset (P.vertex_mem_boundary i)))
  exact ⟨β, ⟨hβ.1, hβ.2.trans_le (min_le_right _ _)⟩, d, hd, hdplane,
    hdcontact, hball, hcontact, hheight, hdU,
    convexJoin_subset (singleton_subset_iff.mpr hpU) hdU hUcv⟩

end Homeomorph

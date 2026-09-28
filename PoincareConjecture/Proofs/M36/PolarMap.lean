import PoincareConjecture.Proofs.M36.RadialInverse

set_option autoImplicit false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M36

noncomputable def radialPolarPoint (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) : StandardCapSpace :=
  radialEuclideanRadius g₀ z.2 • z.1.1

theorem radialPolarPoint_contMDiff (g₀ : StandardInitialMetric) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (radialPolarPoint g₀) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp⟩
  have hs : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : StandardCylinderSpace => radialEuclideanRadius g₀ z.2) :=
    (radialEuclideanRadius_contDiff g₀).contMDiff.comp contMDiff_snd
  have ht : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun z : StandardCylinderSpace => z.1.1) :=
    (contMDiff_coe_sphere (E := StandardCapSpace) (n := 2)).comp contMDiff_fst
  exact hs.smul ht

theorem radialPolarPoint_continuous (g₀ : StandardInitialMetric) :
    Continuous (radialPolarPoint g₀) := (radialPolarPoint_contMDiff g₀).continuous

theorem radialPolarPoint_zero (g₀ : StandardInitialMetric) (theta : UnitTwoSphere) :
    radialPolarPoint g₀ (theta, 0) = 0 := by
  simp [radialPolarPoint, radialEuclideanRadius_zero]

theorem radialPolarPoint_norm (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hs : 0 ≤ z.2) :
    ‖radialPolarPoint g₀ z‖ = radialEuclideanRadius g₀ z.2 := by
  have hnorm : ‖z.1.1‖ = 1 := by simp
  have hr : 0 ≤ radialEuclideanRadius g₀ z.2 := by
    simpa only [radialEuclideanRadius_zero] using
      (radialEuclideanRadius_strictMono g₀).monotone hs
  simp [radialPolarPoint, norm_smul, hnorm, abs_of_nonneg hr]

theorem radialArclength_norm_polar (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hs : 0 ≤ z.2) :
    radialArclength g₀ ‖radialPolarPoint g₀ z‖ = z.2 := by
  rw [radialPolarPoint_norm g₀ z hs, radialArclength_euclideanRadius]

theorem radialPolarPoint_injOn (g₀ : StandardInitialMetric) :
    Set.InjOn (radialPolarPoint g₀) (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
  intro z hz w hw h
  have hs := congrArg (fun x : StandardCapSpace => radialArclength g₀ ‖x‖) h
  rw [radialArclength_norm_polar g₀ z hz.2.le,
    radialArclength_norm_polar g₀ w hw.2.le] at hs
  apply Prod.ext _ hs
  apply Subtype.ext
  have hr : radialEuclideanRadius g₀ z.2 ≠ 0 :=
    ((radialEuclideanRadius_pos_iff g₀ z.2).mpr hz.2).ne'
  apply smul_right_injective StandardCapSpace hr
  simpa only [radialPolarPoint, ← hs] using h

noncomputable def clippedRadialCollapse (g₀ : StandardInitialMetric)
    (A : ℝ) (z : StandardCylinderSpace) : StandardCapSpace :=
  radialPolarPoint g₀ (z.1, max (A - z.2) 0)

theorem clippedRadialCollapse_continuous (g₀ : StandardInitialMetric) (A : ℝ) :
    Continuous (clippedRadialCollapse g₀ A) :=
  (radialPolarPoint_continuous g₀).comp
    (continuous_fst.prodMk ((continuous_const.sub continuous_snd).max continuous_const))

theorem clippedRadialCollapse_of_lt (g₀ : StandardInitialMetric) (A : ℝ)
    (z : StandardCylinderSpace) (hz : z.2 < A) :
    clippedRadialCollapse g₀ A z = radialPolarPoint g₀ (z.1, A - z.2) := by
  simp [clippedRadialCollapse, max_eq_left (sub_pos.mpr hz).le]

theorem clippedRadialCollapse_of_le (g₀ : StandardInitialMetric) (A : ℝ)
    (z : StandardCylinderSpace) (hz : A ≤ z.2) :
    clippedRadialCollapse g₀ A z = 0 := by
  simp [clippedRadialCollapse, max_eq_right (sub_nonpos.mpr hz), radialPolarPoint_zero]

theorem clippedRadialCollapse_contMDiffOn (g₀ : StandardInitialMetric) (A : ℝ) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (clippedRadialCollapse g₀ A) {z | z.2 < A} := by
  have h : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (fun z : StandardCylinderSpace => radialPolarPoint g₀ (z.1, A - z.2)) :=
    (radialPolarPoint_contMDiff g₀).comp
      (contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd))
  apply h.contMDiffOn.congr
  intro z hz
  exact clippedRadialCollapse_of_lt g₀ A z hz

theorem radialArclength_norm_collapse (g₀ : StandardInitialMetric) (A : ℝ)
    (z : StandardCylinderSpace) :
    radialArclength g₀ ‖clippedRadialCollapse g₀ A z‖ = max (A - z.2) 0 :=
  radialArclength_norm_polar g₀ _ (le_max_right _ _)

end PoincareConjecture.M36

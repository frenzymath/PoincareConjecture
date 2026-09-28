import PoincareConjecture.Proofs.M36.PolarMap
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M36

noncomputable def radialDirection (x : StandardCapSpace) : UnitTwoSphere :=
  if hx : x = 0 then ⟨axisBasis 0, by simp [axisBasis]⟩
  else ⟨‖x‖⁻¹ • x, by simp [norm_smul, norm_ne_zero_iff.mpr hx]⟩

theorem radialDirection_val (x : StandardCapSpace) (hx : x ≠ 0) :
    (radialDirection x).1 = ‖x‖⁻¹ • x := by simp [radialDirection, hx]

theorem radialDirection_contMDiffOn :
    ContMDiffOn (𝓡 3) (𝓡 2) ∞ radialDirection ({0}ᶜ : Set StandardCapSpace) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp⟩
  let U : TopologicalSpace.Opens StandardCapSpace := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hs : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun x : U => ‖x.1‖⁻¹ • x.1) := by
    intro x
    have hx : x.1 ≠ 0 := x.2
    exact (((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul
      contDiffAt_id).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt
  have hunit : ∀ x : U, ‖x.1‖⁻¹ • x.1 ∈ Metric.sphere (0 : StandardCapSpace) 1 := by
    intro x
    have hx : x.1 ≠ 0 := x.2
    simp [norm_smul, norm_ne_zero_iff.mpr hx]
  have hdir : ContMDiff (𝓡 3) (𝓡 2) ∞ (fun x : U => radialDirection x.1) := by
    convert! hs.codRestrict_sphere (n := 2) hunit using 1
    funext x
    apply Subtype.ext
    exact radialDirection_val x.1 x.2
  intro x hx
  exact (contMDiffAt_subtype_iff.mp (hdir (⟨x, hx⟩ : U))).contMDiffWithinAt

noncomputable def radialInverseCoordinates (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) : StandardCylinderSpace :=
  (radialDirection x, radialArclength g₀ ‖x‖)

theorem radialInverseCoordinates_contMDiffOn (g₀ : StandardInitialMetric) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (radialInverseCoordinates g₀) ({0}ᶜ : Set StandardCapSpace) := by
  apply radialDirection_contMDiffOn.prodMk
  intro x hx
  have hx0 : x ≠ 0 := by simpa using hx
  exact ((radialArclength_contDiff g₀).contDiffAt.comp x
    (contDiffAt_norm ℝ hx0)).contMDiffAt.contMDiffWithinAt

theorem radialPolarPoint_ne_zero (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 < z.2) : radialPolarPoint g₀ z ≠ 0 := by
  apply norm_pos_iff.mp
  rw [radialPolarPoint_norm g₀ z hz.le]
  exact (radialEuclideanRadius_pos_iff g₀ z.2).mpr hz

theorem radialDirection_polar (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 < z.2) :
    radialDirection (radialPolarPoint g₀ z) = z.1 := by
  apply Subtype.ext
  rw [radialDirection_val _ (radialPolarPoint_ne_zero g₀ z hz),
    radialPolarPoint_norm g₀ z hz.le]
  change (radialEuclideanRadius g₀ z.2)⁻¹ •
    (radialEuclideanRadius g₀ z.2 • z.1.1) = z.1.1
  simp [smul_smul, ((radialEuclideanRadius_pos_iff g₀ z.2).mpr hz).ne']

theorem radialInverseCoordinates_polar (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 < z.2) :
    radialInverseCoordinates g₀ (radialPolarPoint g₀ z) = z := by
  apply Prod.ext
  · exact radialDirection_polar g₀ z hz
  · exact radialArclength_norm_polar g₀ z hz.le

theorem radialPolarPoint_inverse (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) (hx : x ≠ 0) :
    radialPolarPoint g₀ (radialInverseCoordinates g₀ x) = x := by
  change radialEuclideanRadius g₀ (radialArclength g₀ ‖x‖) • (radialDirection x).1 = x
  rw [radialEuclideanRadius_arclength, radialDirection_val x hx]
  simp [smul_smul, norm_ne_zero_iff.mpr hx]

noncomputable def radialPolarChart (g₀ : StandardInitialMetric) :
    OpenPartialHomeomorph StandardCylinderSpace StandardCapSpace where
  toFun := radialPolarPoint g₀
  invFun := radialInverseCoordinates g₀
  source := Set.univ ×ˢ Set.Ioi (0 : ℝ)
  target := {0}ᶜ
  map_source' z hz := by simpa using radialPolarPoint_ne_zero g₀ z hz.2
  map_target' x hx := ⟨Set.mem_univ _, radialArclength_pos g₀
    (norm_pos_iff.mpr (by simpa using hx))⟩
  left_inv' z hz := radialInverseCoordinates_polar g₀ z hz.2
  right_inv' x hx := radialPolarPoint_inverse g₀ x (by simpa using hx)
  open_source := isOpen_univ.prod isOpen_Ioi
  open_target := isOpen_compl_singleton
  continuousOn_toFun := (radialPolarPoint_continuous g₀).continuousOn
  continuousOn_invFun := (radialInverseCoordinates_contMDiffOn g₀).continuousOn

end PoincareConjecture.M36

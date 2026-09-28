import PoincareConjecture.Proofs.M36.CylindricalSphere









set_option autoImplicit false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M36

noncomputable def adaptedPolarPoint (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) : StandardCapSpace :=
  radialPolarPoint g₀ (cylindricalBoundaryDirection g₀ z.1, z.2)

noncomputable def adaptedInverseCoordinates (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) : StandardCylinderSpace :=
  (cylindricalBoundaryInverse g₀ (radialDirection x), radialArclength g₀ ‖x‖)

theorem adaptedPolarPoint_contMDiff (g₀ : StandardInitialMetric) :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (adaptedPolarPoint g₀) :=
  (radialPolarPoint_contMDiff g₀).comp
    (((cylindricalBoundaryDirection_contMDiff g₀).comp contMDiff_fst).prodMk contMDiff_snd)

theorem adaptedInverseCoordinates_contMDiffOn (g₀ : StandardInitialMetric) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (adaptedInverseCoordinates g₀) ({0}ᶜ : Set StandardCapSpace) := by
  have hT : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : StandardCylinderSpace => (cylindricalBoundaryInverse g₀ z.1, z.2)) :=
    ((cylindricalBoundaryInverse_contMDiff g₀).comp contMDiff_fst).prodMk contMDiff_snd
  exact hT.comp_contMDiffOn (radialInverseCoordinates_contMDiffOn g₀)

theorem adaptedPolarPoint_ne_zero (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 < z.2) : adaptedPolarPoint g₀ z ≠ 0 :=
  radialPolarPoint_ne_zero g₀ _ hz

theorem adaptedInverseCoordinates_polar (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : 0 < z.2) :
    adaptedInverseCoordinates g₀ (adaptedPolarPoint g₀ z) = z := by
  apply Prod.ext
  · change cylindricalBoundaryInverse g₀ (radialDirection (adaptedPolarPoint g₀ z)) = z.1
    rw [adaptedPolarPoint,
      radialDirection_polar g₀ (cylindricalBoundaryDirection g₀ z.1, z.2) hz]
    exact cylindricalBoundary_left_inverse g₀ z.1
  · exact radialArclength_norm_polar g₀ _ hz.le

theorem adaptedPolarPoint_inverse (g₀ : StandardInitialMetric)
    (x : StandardCapSpace) (hx : x ≠ 0) :
    adaptedPolarPoint g₀ (adaptedInverseCoordinates g₀ x) = x := by
  change radialPolarPoint g₀ (cylindricalBoundaryDirection g₀
    (cylindricalBoundaryInverse g₀ (radialDirection x)), radialArclength g₀ ‖x‖) = x
  rw [cylindricalBoundary_right_inverse g₀ (radialDirection x)]
  exact radialPolarPoint_inverse g₀ x hx

noncomputable def adaptedPolarChart (g₀ : StandardInitialMetric) :
    OpenPartialHomeomorph StandardCylinderSpace StandardCapSpace where
  toFun := adaptedPolarPoint g₀
  invFun := adaptedInverseCoordinates g₀
  source := Set.univ ×ˢ Set.Ioi (0 : ℝ)
  target := {0}ᶜ
  map_source' z hz := by simpa using adaptedPolarPoint_ne_zero g₀ z hz.2
  map_target' x hx := ⟨Set.mem_univ _, radialArclength_pos g₀
    (norm_pos_iff.mpr (by simpa using hx))⟩
  left_inv' z hz := adaptedInverseCoordinates_polar g₀ z hz.2
  right_inv' x hx := adaptedPolarPoint_inverse g₀ x (by simpa using hx)
  open_source := isOpen_univ.prod isOpen_Ioi
  open_target := isOpen_compl_singleton
  continuousOn_toFun := (adaptedPolarPoint_contMDiff g₀).continuous.continuousOn
  continuousOn_invFun := (adaptedInverseCoordinates_contMDiffOn g₀).continuousOn

noncomputable def adaptedClippedCollapse (g₀ : StandardInitialMetric)
    (A : ℝ) (z : StandardCylinderSpace) : StandardCapSpace :=
  clippedRadialCollapse g₀ A (cylindricalBoundaryDirection g₀ z.1, z.2)

theorem adaptedClippedCollapse_continuous (g₀ : StandardInitialMetric) (A : ℝ) :
    Continuous (adaptedClippedCollapse g₀ A) :=
  (clippedRadialCollapse_continuous g₀ A).comp
    (((cylindricalBoundaryDirection_contMDiff g₀).continuous.comp continuous_fst).prodMk
      continuous_snd)

theorem adaptedClippedCollapse_contMDiffOn (g₀ : StandardInitialMetric) (A : ℝ) :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞
      (adaptedClippedCollapse g₀ A) {z | z.2 < A} :=
  (clippedRadialCollapse_contMDiffOn g₀ A).comp
    ((((cylindricalBoundaryDirection_contMDiff g₀).comp contMDiff_fst).prodMk
      contMDiff_snd).contMDiffOn) (fun _ hz => hz)

theorem adaptedClippedCollapse_tail (g₀ : StandardInitialMetric) (A : ℝ)
    (z : StandardCylinderSpace) (hz : A ≤ z.2) : adaptedClippedCollapse g₀ A z = 0 :=
  clippedRadialCollapse_of_le g₀ A _ hz

theorem adaptedClippedCollapse_arclength (g₀ : StandardInitialMetric) (A : ℝ)
    (z : StandardCylinderSpace) :
    radialArclength g₀ ‖adaptedClippedCollapse g₀ A z‖ = max (A - z.2) 0 :=
  radialArclength_norm_collapse g₀ A _

theorem adaptedClippedCollapse_end (g₀ : StandardInitialMetric)
    (z : StandardCylinderSpace) (hz : z.2 ≤ 4) :
    adaptedClippedCollapse g₀ (g₀.cylindrical_end.radius + 4) z =
      g₀.cylindrical_end.coordinate (z.1, 4 - z.2) := by
  unfold adaptedClippedCollapse
  rw [clippedRadialCollapse_of_lt g₀ _ _
    (by linarith [g₀.cylindrical_end.radius_pos]),
    cylindrical_coordinate_radial g₀ (z.1, 4 - z.2) (sub_nonneg.mpr hz)]
  change radialEuclideanRadius g₀ (g₀.cylindrical_end.radius + 4 - z.2) •
    (cylindricalBoundaryDirection g₀ z.1).1 =
      radialEuclideanRadius g₀ (g₀.cylindrical_end.radius + (4 - z.2)) •
        (cylindricalBoundaryDirection g₀ z.1).1
  rw [add_sub_assoc]

end PoincareConjecture.M36

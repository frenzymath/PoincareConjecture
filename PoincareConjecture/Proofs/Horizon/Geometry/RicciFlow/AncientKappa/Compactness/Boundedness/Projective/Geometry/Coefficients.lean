import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Geometry.FirstJet
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Projective.Diameter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Ellipticity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open Poincare.Geometry.Riemannian.SpaceForm
open scoped Topology Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.CylinderCover

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

def centeredParametrization (f : RoundCylinderSpace → M) (q : UnitTwoSphere)
    (y : RoundCylinderCoordinates) : M :=
  f ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm y.1, y.2)

def normalizedCenteredCoefficients (g : RiemannianMetric 3 M)
    (f : RoundCylinderSpace → M) (Q : ℝ) (q : UnitTwoSphere)
    (y : RoundCylinderCoordinates) :
    RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ :=
  Q • g.parametrizedCoefficients (centeredParametrization f q) y

omit [IsManifold (𝓡 3) ∞ M] in
theorem centeredParametrization_contMDiffAt
    {f : RoundCylinderSpace → M} {ε : ℝ}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (q : UnitTwoSphere) {y : RoundCylinderCoordinates}
    (hy : y.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞
      (centeredParametrization f q) y := by
  exact (hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds
    ⟨mem_univ _, hy⟩)).comp y (cylinderChart_symm_smooth q y)

theorem normalizedCenteredCoefficients_contDiffAt
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε : ℝ}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (Q : ℝ) (q : UnitTwoSphere) {y : RoundCylinderCoordinates}
    (hy : y.2 ∈ Ioo (-ε⁻¹) ε⁻¹) :
    ContDiffAt ℝ ∞ (normalizedCenteredCoefficients g f Q q) y :=
  (g.contDiffAt_parametrizedCoefficients
    (centeredParametrization_contMDiffAt hf q hy)).const_smul _

theorem normalizedCenteredCoefficients_basis_eventuallyEq
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε : ℝ}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (Q : ℝ) (q : UnitTwoSphere) {y : RoundCylinderCoordinates}
    (hy : y.2 ∈ Ioo (-ε⁻¹) ε⁻¹) (i j : Fin 3) :
    (fun p => roundCylinderTensorCoefficient
      (fun z v w => Q * roundCylinderPullback g f z v w)
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j) =ᶠ[𝓝 y]
    (fun p => normalizedCenteredCoefficients g f Q q p
      (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) := by
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (isOpen_Ioo.mem_nhds hy)] with p hp
  change Q * roundCylinderTensorCoefficient (roundCylinderPullback g f)
    (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j = _
  have hp' : ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2) ∈
      univ ×ˢ Ioo (-ε⁻¹) ε⁻¹ := ⟨mem_univ _, hp⟩
  rw [roundCylinderTensorCoefficient_pullback_eq g q f p
    ((hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp')).mdifferentiableAt (by simp))]
  rfl

theorem norm_fderiv_normalizedCenteredCoefficients_le
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε Q : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0 (fun z v w => Q * roundCylinderPullback g f z v w))
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹) :
    ‖fderiv ℝ (normalizedCenteredCoefficients g f Q q) (0, s)‖ ≤ 216 * ε := by
  have hB := (normalizedCenteredCoefficients_contDiffAt g hf Q q (y := (0, s)) hs).differentiableAt (by simp)
  have hcomponent (i j k : Fin 3) :
      ‖fderiv ℝ (normalizedCenteredCoefficients g f Q q) (0, s)
        (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)
        (roundCylinderCoordinateBasis k)‖ ≤ 8 * ε := by
    have h := roundCylinderClose_coefficient_derivative_center_le hε hεone hclose q hs i j k
    rw [(normalizedCenteredCoefficients_basis_eventuallyEq g hf Q q
      (y := (0, s)) hs j k).fderiv_eq, fderiv_bilinear_evaluation hB] at h
    exact h
  have h₁ (i j : Fin 3) :
      ‖fderiv ℝ (normalizedCenteredCoefficients g f Q q) (0, s)
        (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)‖ ≤ 24 * ε := by
    convert norm_le_of_cylinder_basis_bound _ (show 0 ≤ 8 * ε from by positivity)
      (hcomponent i j) using 1
    ring
  have h₂ (i : Fin 3) :
      ‖fderiv ℝ (normalizedCenteredCoefficients g f Q q) (0, s)
        (roundCylinderCoordinateBasis i)‖ ≤ 72 * ε := by
    convert norm_le_of_cylinder_basis_bound _ (show 0 ≤ 24 * ε from by positivity)
      (h₁ i) using 1
    ring
  convert norm_le_of_cylinder_basis_bound _ (show 0 ≤ 72 * ε from by positivity) h₂ using 1
  ring

theorem centered_coefficients_eq_pullback
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε : ℝ}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (Q : ℝ) (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v w : RoundCylinderCoordinates) :
    normalizedCenteredCoefficients g f Q q (0, s) v w =
      Q * roundCylinderPullback g f (q, s)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1, v.2)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 w.1, w.2) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let T : RoundCylinderCoordinates →L[ℝ] RoundCylinderTangent (q, s) :=
    ((mfderiv (𝓡 2) (𝓡 2) c.symm 0).comp
      (ContinuousLinearMap.fst ℝ _ _)).prod (ContinuousLinearMap.snd ℝ _ _)
  let P := (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) f (q, s)).comp T
  let : NormedAddCommGroup (TangentSpace (𝓡 3) (f (q, s))) := by
    unfold TangentSpace
    infer_instance
  let : NormedSpace ℝ (TangentSpace (𝓡 3) (f (q, s))) := by
    unfold TangentSpace
    infer_instance
  let B := Q • (g.inner (f (q, s))).bilinearComp P P
  have hb (i j : Fin 3) :
      normalizedCenteredCoefficients g f Q q (0, s)
          (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) =
        B (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) := by
    have h := (normalizedCenteredCoefficients_basis_eventuallyEq g hf Q q
      (y := (0, s)) hs i j).self_of_nhds
    have h' := h.symm
    dsimp only [roundCylinderTensorCoefficient] at h'
    erw [sphere_chart_symm_zero] at h'
    exact h'
  change normalizedCenteredCoefficients g f Q q (0, s) v w = B v w
  rw [cylinderCoordinate_decomposition v, cylinderCoordinate_decomposition w]
  simp only [map_add, map_smul, add_apply, smul_apply, hb]

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]

theorem normalizedCenteredCoefficients_lower
    (g : RiemannianMetric 3 M) {f : RoundCylinderSpace → M} {ε Q : ℝ}
    (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-ε⁻¹) ε⁻¹))
    (hclose : RoundCylinderClose ε 0 (fun z v w => Q * roundCylinderPullback g f z v w))
    (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-ε⁻¹) ε⁻¹)
    (v : RoundCylinderCoordinates) :
    (1 - ε) * ‖v‖ ^ 2 ≤ normalizedCenteredCoefficients g f Q q (0, s) v v := by
  rw [centered_coefficients_eq_pullback g hf Q q hs v v]
  let u : RoundCylinderTangent (q, s) :=
    (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1, v.2)
  have h := (abs_le.mp (roundCylinderClose_scaled_pullback_quadratic_error
    g f hε hclose (z := (q, s)) hs u)).1
  have hmodel : ‖v‖ ^ 2 ≤ EvolvingRoundCylinderMetric 0 (q, s) u u := by
    have hinner := roundSphereMetric_chart_symm_inner q 0 v.1 v.1
    rw [sphere_chart_symm_zero] at hinner
    change ‖v‖ ^ 2 ≤ 2 * (1 - 0) * (roundSphereMetric 2).inner q
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1)
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0 v.1) + v.2 * v.2
    erw [hinner]
    simpa only [roundCylinderModelCoefficients_apply, sub_zero, mul_one, mul_assoc] using
      (roundCylinderModelCoefficients_center_quadratic_bounds s v).1
  have hm := mul_le_mul_of_nonneg_left hmodel (sub_nonneg.mpr hεone)
  nlinarith

end PoincareConjecture.CylinderCover

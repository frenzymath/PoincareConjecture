import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalAssembly
import PoincareConjecture.Definitions.M45NeckGluing

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open PoincareConjecture.Proofs.M47

theorem roundCylinderTensorCoefficient_congr_at {B B' : RoundCylinderTwoTensor}
    {c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2))}
    {p : RoundCylinderCoordinates}
    (h : ∀ v w, B' (c.symm p.1, p.2) v w = B (c.symm p.1, p.2) v w) (a b : Fin 3) :
    roundCylinderTensorCoefficient B' c p a b = roundCylinderTensorCoefficient B c p a b := by
  unfold roundCylinderTensorCoefficient
  exact h _ _

theorem roundCylinderIteratedDerivative_eq_on {t : ℝ}
    {c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2))}
    {B B' : RoundCylinderTwoTensor} {O : Set RoundCylinderCoordinates} (hO : IsOpen O)
    (hcoef : ∀ p ∈ O, ∀ a b : Fin 3,
      roundCylinderTensorCoefficient B' c p a b = roundCylinderTensorCoefficient B c p a b) :
    ∀ k : ℕ, ∀ p ∈ O,
      roundCylinderIteratedDerivative t c B' k p = roundCylinderIteratedDerivative t c B k p := by
  intro k
  induction k with
  | zero =>
    intro p hp
    funext a
    simp only [roundCylinderIteratedDerivative, hcoef p hp]
  | succ k ih =>
    intro p hp
    funext a
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
    have hev : (fun q => roundCylinderIteratedDerivative t c B' k q (fun i => a i.succ)) =ᶠ[𝓝 p]
        (fun q => roundCylinderIteratedDerivative t c B k q (fun i => a i.succ)) := by
      filter_upwards [hO.mem_nhds hp] with q hq
      rw [ih q hq]
    have hfd := hev.fderiv_eq (𝕜 := ℝ)
    rw [ih p hp]
    congr 1
    exact congrArg (fun L => L (roundCylinderCoordinateBasis (a 0))) hfd

theorem roundCylinderFamilyClose_congr_on {epsilon : ℝ} {I : Set ℝ}
    {B B' : ℝ → RoundCylinderTwoTensor} (h : RoundCylinderFamilyClose epsilon I B)
    (heq : ∀ s ∈ I, ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ →
      ∀ v w, B' s z v w = B s z v w) :
    RoundCylinderFamilyClose epsilon I B' := by
  obtain ⟨hsmooth, bound, hbound, herror⟩ := h
  refine ⟨fun s hs q a b => ?_, bound, hbound, fun s hs z hz => ?_⟩
  · refine (hsmooth s hs q a b).congr ?_
    intro p hp
    exact roundCylinderTensorCoefficient_congr_at (fun v w => heq s hs _ hp.2 v w) a b
  · have hO : IsOpen ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
        Ioo (-epsilon⁻¹) epsilon⁻¹) :=
      (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).open_target.prod isOpen_Ioo
    have hcoef : ∀ p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
        Ioo (-epsilon⁻¹) epsilon⁻¹, ∀ a b : Fin 3,
        roundCylinderTensorCoefficient (B' s) (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b =
          roundCylinderTensorCoefficient (B s) (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) p a b :=
      fun p hp a b => roundCylinderTensorCoefficient_congr_at
        (fun v w => heq s hs _ hp.2 v w) a b
    have hp : (((chartAt (EuclideanSpace ℝ (Fin 2)) z.1) z.1, z.2) : RoundCylinderCoordinates) ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ :=
      ⟨(chartAt (EuclideanSpace ℝ (Fin 2)) z.1).map_source (mem_chart_source _ z.1), hz⟩
    have key : roundCylinderJetErrorSquared s (B' s) ⌊epsilon⁻¹⌋₊ z =
        roundCylinderJetErrorSquared s (B s) ⌊epsilon⁻¹⌋₊ z := by
      simp only [roundCylinderJetErrorSquared]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [roundCylinderIteratedDerivative_eq_on hO hcoef k _ hp]
    rw [key]
    exact herror s hs z hz

theorem surgeryCanonicalControl_of_neck_gluing_family_on {epsilon beta : ℝ}
    (hglue : M45NeckGluingProperty.{u} epsilon beta) (I : M45NeckGluingInput.{u} epsilon beta)
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}} {origin Cc : ℝ}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g) (hNeps : N.epsilon = epsilon)
    (e : SurgeryFlowCylinder F C origin (N.scale⁻¹ ^ 2) (Ioc (-1 : ℝ) 0) N.carrier)
    (hscalar : (F.connection (origin + 0 / (N.scale⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 (by constructor <;> norm_num) N.center) =
        N.connection.scalarCurvature N.center)
    (hpull : ∀ s ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ v w,
        surgeryCylinderPullback e N.coordinate_map s z v w =
          I.piecewiseTensor I.recent_patch.coordinate s z v w) :
    SurgeryCanonicalControl F (origin + 0 / (N.scale⁻¹ ^ 2))
      (e.forward 0 (by constructor <;> norm_num) N.center) epsilon Cc := by
  obtain ⟨G⟩ := hglue I
  have hclose := G.comparison
  rw [G.coordinate_eq] at hclose
  have hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback e N.coordinate_map) := by
    rw [hNeps]
    exact roundCylinderFamilyClose_congr_on hclose hpull
  obtain ⟨S, hS⟩ := exists_physical_strong_neck_of_family N e hscalar hfamily
  rw [← hNeps]
  exact SurgeryCanonicalControl.neck S hS

end PoincareConjecture.M47

import PoincareConjecture.Proofs.M08.BackwardEulerTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

def squareExtensionOfBackward {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo τ₁ τ₂) p.curve
      (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂))) :
    ParametricAlongCurveExtensionOn (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (squareReparameterizedCurve p.curve)
      (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))) where
  extension s y := (2 * s) • E.extension (s ^ 2) y
  domain := {z : ℝ × M | (z.1 ^ 2, z.2) ∈ E.domain}
  open_domain := by
    apply E.open_domain.preimage
    fun_prop
  graph_mem s hs := E.graph_mem _ (sq_mem_backward_interior p.nonnegative hs).2
  smooth z hz := by
    apply ContMDiffAt.contMDiffWithinAt
    exact parametricExtension_contMDiffAt_smul_reparam E
      (f := fun s ↦ s ^ 2) (c := fun s ↦ 2 * s) hz
      (contDiffAt_id.pow 2) (contDiffAt_const.mul contDiffAt_id)
  agrees s hs := by
    change (2 * s) • E.extension (s ^ 2) (p.curve (s ^ 2)) = _
    rw [E.agrees _ (sq_mem_backward_interior p.nonnegative hs).2,
      squarePath_velocityWithin p hs]

theorem squareExtensionOfBackward_deriv {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo τ₁ τ₂) p.curve
      (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂))) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    deriv (fun r ↦ (squareExtensionOfBackward p E).extension r (p.curve (s ^ 2))) s =
      (4 * s ^ 2) • deriv (fun r ↦ E.extension r (p.curve (s ^ 2))) (s ^ 2) +
        (2 : ℝ) • curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2) := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (p.curve (s ^ 2))) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (p.curve (s ^ 2))) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  have hτ := (sq_mem_backward_interior p.nonnegative hs).2
  have htime := (parametricExtension_differentiableAt_time E (E.graph_mem _ hτ)).hasDerivAt
  have hsq : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hscale : HasDerivAt (fun r : ℝ ↦ 2 * r) 2 s := by
    simpa using (hasDerivAt_id s).const_mul 2
  have hd := (hscale.smul (htime.scomp s (h := fun r : ℝ ↦ r ^ 2) hsq)).deriv
  change deriv (fun r ↦ (2 * r) • E.extension (r ^ 2) (p.curve (s ^ 2))) s = _
  simpa only [Pi.smul_def', Function.comp_def, E.agrees _ hτ, smul_smul,
    show 2 * s * (2 * s) = 4 * s ^ 2 by ring] using hd

theorem squareExtensionOfBackward_connection {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo τ₁ τ₂) p.curve
      (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂))) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    (F.connection (T - s ^ 2)).connection
        ((squareExtensionOfBackward p E).extension s) (p.curve (s ^ 2))
        (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
          (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) s) =
      (4 * s ^ 2) • (F.connection (T - s ^ 2)).connection (E.extension (s ^ 2))
        (p.curve (s ^ 2))
        (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2)) := by
  have hτ := (sq_mem_backward_interior p.nonnegative hs).2
  have hspace := (parametricExtension_contMDiffAt_space E (E.graph_mem _ hτ)).mdifferentiableAt
    (by norm_num)
  have hcov := (F.connection (T - s ^ 2)).connection.isCovariantDerivativeOn.smul_const
    (2 * s) hspace
  change (F.connection (T - s ^ 2)).connection ((2 * s) • E.extension (s ^ 2))
    (p.curve (s ^ 2)) _ = _
  rw [hcov, squarePath_velocityWithin p hs]
  simp only [smul_apply, map_smul, smul_smul,
    show 2 * s * (2 * s) = 4 * s ^ 2 by ring]

theorem pullbackCovariantDerivative_backward_transport {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo τ₁ τ₂) p.curve
      (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂))) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
        (squareReparameterizedCurve p.curve)
        (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
          (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)))
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (squareExtensionOfBackward p E) s =
      (2 : ℝ) • curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2) +
        (4 * s ^ 2) • pullbackCovariantDerivative F (fun r ↦ T - r) p.curve
          (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂))
          (Set.Ioo τ₁ τ₂) E (s ^ 2) := by
  simp only [pullbackCovariantDerivative, squareReparameterizedCurve, smul_add]
  rw [squareExtensionOfBackward_deriv p E hs, squareExtensionOfBackward_connection p E hs]
  abel

theorem regularizedEulerResidual_backward_transport (hM04 : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo τ₁ τ₂) p.curve
      (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂))) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (W : TangentSpace (𝓡 n) (p.curve (s ^ 2))) :
    regularizedEulerResidual F T (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) (squareExtensionOfBackward p E) s W =
      (4 * s ^ 2) * backwardEulerResidual F T p.curve (Set.Ioo τ₁ τ₂) E (s ^ 2) W := by
  have hs0 := (sq_mem_backward_interior p.nonnegative hs).1.ne'
  let G := (F.metric (T - s ^ 2)).inner (p.curve (s ^ 2))
  let X := curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2)
  let A := pullbackCovariantDerivative F (fun r ↦ T - r) p.curve
    (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂)) (Set.Ioo τ₁ τ₂) E (s ^ 2)
  have hmetric : G ((2 : ℝ) • X + (4 * s ^ 2) • A) W =
      2 * G X W + (4 * s ^ 2) * G A W := by
    rw [G.map_add, G.map_smul, G.map_smul]
    rfl
  unfold regularizedEulerResidual backwardEulerResidual
  rw [pullbackCovariantDerivative_backward_transport p E hs, squarePath_velocityWithin p hs]
  rw [ricci_smul_left_of_curvatureTheory hM04]
  unfold scalarCurvatureDifferential squareReparameterizedCurve
  rw [hmetric]
  field_simp [hs0]
  ring

theorem exists_regularizedEuler_extension_of_backward {J : Set ℝ}
    {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (p : BackwardTimePath F T τ₁ τ₂) (hp : IsBackwardLGeodesic F T τ₁ τ₂ p) :
    ∃ E : ParametricAlongCurveExtensionOn (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (squareReparameterizedCurve p.curve)
      (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))),
      ∀ s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
        regularizedLGeodesicEquation F T (squareReparameterizedCurve p.curve)
          (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) E s := by
  obtain ⟨E, hE⟩ := hp
  refine ⟨squareExtensionOfBackward p E, ?_⟩
  intro s hs W
  rw [regularizedEulerResidual_backward_transport hM04 p E hs W,
    hE _ (sq_mem_backward_interior p.nonnegative hs).2 W, mul_zero]

end PoincareConjecture.M08

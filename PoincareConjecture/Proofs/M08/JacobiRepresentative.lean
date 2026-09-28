import PoincareConjecture.Proofs.M08.ChartPullback
import PoincareConjecture.Proofs.M08.JacobiFieldPackaging
import PoincareConjecture.Proofs.M08.SmoothSectionExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem curveVelocityWithin_restrict {C D : Set ℝ} (α : ℝ → M) {s : ℝ}
    (hC : UniqueDiffWithinAt ℝ C s) (hD : UniqueDiffWithinAt ℝ D s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    curveVelocityWithin (n := n) α C s = curveVelocityWithin (n := n) α D s := by
  unfold curveVelocityWithin
  rw [mfderivWithin_eq_mfderiv hC.uniqueMDiffWithinAt hα,
    mfderivWithin_eq_mfderiv hD.uniqueMDiffWithinAt hα]

theorem pullbackCovariantDerivative_restrict {J C D : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)} (hDC : D ⊆ C)
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ}
    (hC : UniqueDiffWithinAt ℝ C s) (hD : UniqueDiffWithinAt ℝ D s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y C E s =
      pullbackCovariantDerivative F time α Y D (restrictParametricSectionExtension hDC E) s := by
  unfold pullbackCovariantDerivative restrictParametricSectionExtension
  rw [curveVelocityWithin_restrict α hC hD hα]

theorem pullbackCovariantDerivative_restrict_congr {J C D : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)} (hDC : D ⊆ C)
    (EC : ParametricAlongCurveExtensionOn C α Y)
    (ED : ParametricAlongCurveExtensionOn D α Y) {s : ℝ} (hs : s ∈ D)
    (hC : UniqueDiffWithinAt ℝ C s) (hD : UniqueDiffWithinAt ℝ D s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y C EC s =
      pullbackCovariantDerivative F time α Y D ED s := by
  rw [pullbackCovariantDerivative_restrict F time hDC EC hC hD hα]
  exact pullbackCovariantDerivative_extension_independent F time
    (restrictParametricSectionExtension hDC EC) ED hs hD hα

theorem tangent_cast_eq {x y : M} (h : x = y) (v : TangentSpace (𝓡 n) x) :
    ((h ▸ v) : TangentSpace (𝓡 n) y) = v := by
  cases h
  rfl

variable {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ}
  {p : BackwardTimePath F T τ₁ τ₂}

theorem sqrtRegularPath_eqOn (R R' : SqrtRegularPath p) :
    EqOn R.curve R'.curve (sqrtParameterInterval τ₁ τ₂) :=
  fun s hs ↦ (R.agrees s hs).trans (R'.agrees s hs).symm

theorem sqrtRegularPath_mdifferentiableAt (R : SqrtRegularPath p) {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) R.curve s :=
  ((R.smooth s (R.interval_subset hs)).contMDiffAt
    (R.open_domain.mem_nhds (R.interval_subset hs))).mdifferentiableAt (by simp)

theorem sqrtRegularField_field_eq {R R' : SqrtRegularPath p}
    {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R Y) (Q' : SqrtRegularField R' Y) {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂) : Q.field s = Q'.field s := by
  have hQ := (Q.agrees s hs).trans
    (tangent_cast_eq (n := n) (R.agrees s hs).symm (Y (s ^ 2)))
  have hQ' := (Q'.agrees s hs).trans
    (tangent_cast_eq (n := n) (R'.agrees s hs).symm (Y (s ^ 2)))
  exact hQ.trans hQ'.symm

theorem sqrtRegularField_firstDerivative_eq {R R' : SqrtRegularPath p}
    {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R Y) (Q' : SqrtRegularField R' Y) {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂) : Q.firstDerivative s = Q'.firstDerivative s := by
  exact pullbackCovariantDerivative_congr F (fun r ↦ T - r ^ 2)
    (sqrtRegularPath_eqOn R R') (fun r hr ↦ sqrtRegularField_field_eq Q Q' hr)
      Q.extension Q'.extension hs
      (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered) s hs)
      (sqrtRegularPath_mdifferentiableAt R' hs)

theorem sqrtRegularField_secondDerivative_eq {R R' : SqrtRegularPath p}
    {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R Y) (Q' : SqrtRegularField R' Y) {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂) : Q.secondDerivative s = Q'.secondDerivative s := by
  exact pullbackCovariantDerivative_congr F (fun r ↦ T - r ^ 2)
    (sqrtRegularPath_eqOn R R') (fun r hr ↦ sqrtRegularField_firstDerivative_eq Q Q' hr)
      Q.derivative_extension Q'.derivative_extension hs
      (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered) s hs)
      (sqrtRegularPath_mdifferentiableAt R' hs)

def transferSqrtRegularField {R : SqrtRegularPath p}
    {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R Y) (R' : SqrtRegularPath p) : SqrtRegularField R' Y := by
  let E := transferParametricExtension (sqrtRegularPath_eqOn R R') (fun _ _ ↦ rfl) Q.extension
  have hfirst : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, Q.firstDerivative s =
      pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) R'.curve Q.field
        (sqrtParameterInterval τ₁ τ₂) E s := by
    intro s hs
    exact pullbackCovariantDerivative_transfer F (fun r ↦ T - r ^ 2)
      (sqrtRegularPath_eqOn R R') (fun _ _ ↦ rfl) Q.extension hs
  exact {
    field := Q.field
    agrees := fun s hs ↦ ((Q.agrees s hs).trans
      (tangent_cast_eq (n := n) (R.agrees s hs).symm (Y (s ^ 2)))).trans
        (tangent_cast_eq (n := n) (R'.agrees s hs).symm (Y (s ^ 2))).symm
    extension := E
    derivative_extension := transferParametricExtension (sqrtRegularPath_eqOn R R')
      hfirst Q.derivative_extension }

theorem regularizedJacobiResidual_representative_eq
    (R R' : RegularizedLGeodesicData p)
    {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (Q : SqrtRegularField R.path Y) (Q' : SqrtRegularField R'.path Y) {s : ℝ}
    (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (W : TangentSpace (𝓡 n) (R.path.curve s)) :
    regularizedJacobiResidual R Q s W = regularizedJacobiResidual R' Q' s W := by
  have hcurve := sqrtRegularPath_eqOn R.path R'.path
  have hfield := sqrtRegularField_field_eq Q Q' hs
  have hfirst := sqrtRegularField_firstDerivative_eq Q Q' hs
  have hsecond := sqrtRegularField_secondDerivative_eq Q Q' hs
  have hvelocity := curveVelocityWithin_congr (n := n) hcurve hs
  unfold regularizedJacobiResidual
  rw [hcurve hs, hfield, hfirst, hsecond, hvelocity]

theorem hasLJacobiInitialDerivative_representative_iff
    (R R' : RegularizedLGeodesicData p)
    (Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ))
    (Z : TangentSpace (𝓡 n) (p.curve τ₁)) :
    HasLJacobiInitialDerivative R Y Z ↔ HasLJacobiInitialDerivative R' Y Z := by
  have htransfer (A B : RegularizedLGeodesicData p) :
      HasLJacobiInitialDerivative A Y Z → HasLJacobiInitialDerivative B Y Z := by
    rintro ⟨Q, hQ⟩
    let Q' := transferSqrtRegularField Q B.path
    refine ⟨Q', ?_⟩
    have hs : Real.sqrt τ₁ ∈ sqrtParameterInterval τ₁ τ₂ :=
      ⟨le_rfl, Real.sqrt_le_sqrt p.ordered.le⟩
    have heq := sqrtRegularField_firstDerivative_eq Q Q' hs
    dsimp only at hQ ⊢
    rw [tangent_cast_eq (n := n)] at hQ ⊢
    exact heq.symm.trans hQ
  exact ⟨htransfer R R', htransfer R' R⟩

theorem isLJacobiField_residual_for_representative
    {Y : ∀ τ, TangentSpace (𝓡 n) (p.curve τ)}
    (hY : IsLJacobiField F T τ₁ τ₂ p Y) (R : RegularizedLGeodesicData p) :
    ∃ Q : SqrtRegularField R.path Y, Y τ₁ = 0 ∧
      ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
        ∀ W : TangentSpace (𝓡 n) (R.path.curve s), regularizedJacobiResidual R Q s W = 0 := by
  obtain ⟨R₀, Q₀, hzero, hres⟩ := hY
  let Q := transferSqrtRegularField Q₀ R.path
  refine ⟨Q, hzero, ?_⟩
  intro s hs W
  rw [← regularizedJacobiResidual_representative_eq R₀ R Q₀ Q hs W]
  exact hres s hs W

end PoincareConjecture.M08

import PoincareConjecture.Proofs.M08.RegularizedAction
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem parametricExtension_differentiableAt_time {I : Set ℝ} {γ : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (γ s)}
    (E : ParametricAlongCurveExtensionOn I γ Y) {s : ℝ} {x : M}
    (h : (s, x) ∈ E.domain) : DifferentiableAt ℝ (fun r ↦ E.extension r x) s := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  have hmap := (E.smooth _ h).contMDiffAt (E.open_domain.mem_nhds h)
  have hslice : ContMDiffAt (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun r ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) x
        (E.extension r x)) s :=
    hmap.comp s (f := fun r : ℝ ↦ (r, x)) (contMDiffAt_id.prodMk contMDiffAt_const)
  have hc : ContDiffAt ℝ ∞
      (fun r ↦ e.continuousLinearMapAt ℝ x (E.extension r x)) s := by
    simpa only [e.continuousLinearMapAt_apply_of_mem ℝ hx] using
      (Bundle.contMDiffAt_totalSpace.mp hslice).2.contDiffAt
  have hi := (e.symmL ℝ x).contDiff.contDiffAt.comp s hc
  simpa only [Function.comp_def, e.symmL_continuousLinearMapAt hx] using
    hi.differentiableAt (by norm_num)

theorem parametricExtension_contMDiffAt_space {I : Set ℝ} {γ : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (γ s)}
    (E : ParametricAlongCurveExtensionOn I γ Y) {s : ℝ} {x : M}
    (h : (s, x) ∈ E.domain) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E.extension s y)) x :=
  ((E.smooth _ h).contMDiffAt (E.open_domain.mem_nhds h)).comp x
    (contMDiffAt_const.prodMk contMDiffAt_id)

theorem parametricExtension_contMDiffAt_smul_reparam {I : Set ℝ} {γ : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (γ s)}
    (E : ParametricAlongCurveExtensionOn I γ Y) {f c : ℝ → ℝ} {z : ℝ × M}
    (h : (f z.1, z.2) ∈ E.domain)
    (hf : ContDiffAt ℝ ∞ f z.1) (hc : ContDiffAt ℝ ∞ c z.1) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun w : ℝ × M ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) w.2
        (c w.1 • E.extension (f w.1) w.2)) z := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) z.2
  have hmap := ((E.smooth _ h).contMDiffAt (E.open_domain.mem_nhds h)).comp z
    ((hf.contMDiffAt.comp z contMDiffAt_fst).prodMk contMDiffAt_snd)
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_snd, ?_⟩
  have hcoord := (Bundle.contMDiffAt_totalSpace.mp hmap).2
  have hprod := (hc.contMDiffAt.comp z contMDiffAt_fst).smul hcoord
  apply hprod.congr_of_eventuallyEq
  have hnear : ∀ᶠ w : ℝ × M in 𝓝 z, w.2 ∈ e.baseSet :=
    continuous_snd.continuousAt (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _))
  filter_upwards [hnear] with w hw
  change (e ⟨w.2, c w.1 • E.extension (f w.1) w.2⟩).2 =
    c w.1 • (e ⟨w.2, E.extension (f w.1) w.2⟩).2
  simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hw, map_smul]

theorem squarePath_velocityWithin {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) s =
      (2 * s) • curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2) := by
  have hτ := (sq_mem_backward_interior p.nonnegative hs).2
  have hreg := (p.regular _ hτ).contMDiffAt (isOpen_Ioo.mem_nhds hτ)
  simp only [curveVelocityWithin, mfderivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hs),
    mfderivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hτ)]
  exact curveVelocity_comp_sq (hreg.mdifferentiableAt one_ne_zero)

theorem sqrt_mem_square_interior {a b τ : ℝ} (ha : 0 ≤ a)
    (hτ : τ ∈ Set.Ioo a b) :
    0 < τ ∧ Real.sqrt τ ∈ Set.Ioo (Real.sqrt a) (Real.sqrt b) := by
  have hpos := ha.trans_lt hτ.1
  exact ⟨hpos, Real.sqrt_lt_sqrt ha hτ.1, Real.sqrt_lt_sqrt hpos.le hτ.2⟩

noncomputable def backwardExtensionOfSquare {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (squareReparameterizedCurve p.curve)
      (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)))) :
    ParametricAlongCurveExtensionOn (Set.Ioo τ₁ τ₂) p.curve
      (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂)) where
  extension τ y := (2 * Real.sqrt τ)⁻¹ • E.extension (Real.sqrt τ) y
  domain := {z : ℝ × M | 0 < z.1 ∧ (Real.sqrt z.1, z.2) ∈ E.domain}
  open_domain := (isOpen_lt continuous_const continuous_fst).inter
    (E.open_domain.preimage ((Real.continuous_sqrt.comp continuous_fst).prodMk continuous_snd))
  graph_mem τ hτ := by
    have hs := sqrt_mem_square_interior p.nonnegative hτ
    refine ⟨hs.1, ?_⟩
    simpa only [squareReparameterizedCurve, Real.sq_sqrt hs.1.le] using
      E.graph_mem _ hs.2
  smooth z hz := by
    apply ContMDiffAt.contMDiffWithinAt
    apply parametricExtension_contMDiffAt_smul_reparam E
      (f := Real.sqrt) (c := fun τ ↦ (2 * Real.sqrt τ)⁻¹) hz.2
      (Real.contDiffAt_sqrt hz.1.ne')
    exact (contDiffAt_const.mul (Real.contDiffAt_sqrt hz.1.ne')).inv
      (mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hz.1).ne')
  agrees τ hτ := by
    have hs := sqrt_mem_square_interior p.nonnegative hτ
    have hsq := Real.sq_sqrt hs.1.le
    have he := E.agrees _ hs.2
    change E.extension (Real.sqrt τ) (p.curve ((Real.sqrt τ) ^ 2)) = _ at he
    have hv := squarePath_velocityWithin p hs.2
    rw [hv, hsq] at he
    rw [he, smul_smul, inv_mul_cancel₀, one_smul]
    exact mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr hs.1).ne'

theorem backwardExtensionOfSquare_deriv {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (squareReparameterizedCurve p.curve)
      (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)))) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    (4 * s ^ 2) • deriv
        (fun r ↦ (backwardExtensionOfSquare p E).extension r (p.curve (s ^ 2))) (s ^ 2) =
      deriv (fun r ↦ E.extension r (p.curve (s ^ 2))) s -
        (2 : ℝ) • curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2) := by
  let : NormedAddCommGroup (TangentSpace (𝓡 n) (p.curve (s ^ 2))) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) (p.curve (s ^ 2))) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  have hpos := (sq_mem_backward_interior p.nonnegative hs).1
  have hs0 := hpos.ne'
  have hsqrt : HasDerivAt Real.sqrt (2 * s)⁻¹ (s ^ 2) := by
    simpa only [Real.sqrt_sq hpos.le, one_div] using
      Real.hasDerivAt_sqrt (pow_ne_zero 2 hs0)
  have hinv : HasDerivAt (fun r : ℝ ↦ (2 * Real.sqrt r)⁻¹)
      (-(2 * (2 * s)⁻¹) / (2 * s) ^ 2) (s ^ 2) := by
    convert! (hsqrt.const_mul 2).inv (by simp [Real.sqrt_sq hpos.le, hs0]) using 1
    simp only [Real.sqrt_sq hpos.le]
  have htime := parametricExtension_differentiableAt_time E (E.graph_mem s hs)
  have he : HasDerivAt (fun r ↦ E.extension r (p.curve (s ^ 2)))
      (deriv (fun r ↦ E.extension r (p.curve (s ^ 2))) s) (Real.sqrt (s ^ 2)) := by
    simpa only [Real.sqrt_sq hpos.le, squareReparameterizedCurve] using htime.hasDerivAt
  have hd : deriv
      (fun r ↦ (2 * Real.sqrt r)⁻¹ • E.extension (Real.sqrt r) (p.curve (s ^ 2)))
      (s ^ 2) =
        (2 * s)⁻¹ • (2 * s)⁻¹ • deriv (fun r ↦ E.extension r (p.curve (s ^ 2))) s +
          (-(2 * (2 * s)⁻¹) / (2 * s) ^ 2) • E.extension s (p.curve (s ^ 2)) := by
    simpa only [Pi.smul_def', Function.comp_def, Real.sqrt_sq hpos.le] using
      (hinv.smul (he.scomp (s ^ 2) hsqrt)).deriv
  have hagree := E.agrees s hs
  rw [squarePath_velocityWithin p hs] at hagree
  change E.extension s (p.curve (s ^ 2)) = _ at hagree
  have hc₁ : (4 * s ^ 2) * ((2 * s)⁻¹ * (2 * s)⁻¹) = 1 := by
    field_simp [hs0]
    ring
  have hc₂ : (4 * s ^ 2) * (-(2 * (2 * s)⁻¹) / (2 * s) ^ 2 * (2 * s)) = -2 := by
    field_simp [hs0]
    ring
  change (4 * s ^ 2) • deriv
    (fun r ↦ (2 * Real.sqrt r)⁻¹ • E.extension (Real.sqrt r) (p.curve (s ^ 2))) (s ^ 2) = _
  rw [hd]
  simp only [hagree, smul_add, smul_smul,
    hc₁, hc₂, one_smul, neg_smul, sub_eq_add_neg]

theorem backwardExtensionOfSquare_connection {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (squareReparameterizedCurve p.curve)
      (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)))) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    (4 * s ^ 2) • (F.connection (T - s ^ 2)).connection
        ((backwardExtensionOfSquare p E).extension (s ^ 2)) (p.curve (s ^ 2))
        (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2)) =
      (F.connection (T - s ^ 2)).connection (E.extension s) (p.curve (s ^ 2))
        (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
          (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) s) := by
  have hpos := (sq_mem_backward_interior p.nonnegative hs).1
  have hspace := (parametricExtension_contMDiffAt_space E (E.graph_mem s hs)).mdifferentiableAt
    (by norm_num)
  have hcov := (F.connection (T - s ^ 2)).connection.isCovariantDerivativeOn.smul_const
    (2 * s)⁻¹ hspace
  dsimp only [squareReparameterizedCurve] at hcov
  change (4 * s ^ 2) • (F.connection (T - s ^ 2)).connection
    (fun y ↦ (2 * Real.sqrt (s ^ 2))⁻¹ • E.extension (Real.sqrt (s ^ 2)) y)
    (p.curve (s ^ 2)) _ = _
  rw [Real.sqrt_sq hpos.le, squarePath_velocityWithin p hs]
  change (4 * s ^ 2) • (F.connection (T - s ^ 2)).connection
    ((2 * s)⁻¹ • E.extension s) (p.curve (s ^ 2)) _ = _
  rw [hcov]
  simp only [smul_apply, map_smul, smul_smul]
  congr 1
  field_simp [hpos.ne']
  ring

theorem pullbackCovariantDerivative_square_transport {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (squareReparameterizedCurve p.curve)
      (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)))) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2)
        (squareReparameterizedCurve p.curve)
        (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
          (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)))
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) E s =
      (2 : ℝ) • curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2) +
        (4 * s ^ 2) • pullbackCovariantDerivative F (fun r ↦ T - r) p.curve
          (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂))
          (Set.Ioo τ₁ τ₂) (backwardExtensionOfSquare p E) (s ^ 2) := by
  simp only [pullbackCovariantDerivative, smul_add]
  rw [backwardExtensionOfSquare_deriv p E hs, backwardExtensionOfSquare_connection p E hs]
  abel

theorem ricci_smul_left_of_curvatureTheory (hM04 : RicciFlowCurvatureTheory.{u})
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (x : M)
    (c : ℝ) (v w : TangentSpace (𝓡 n) x) :
    D.ricci x (c • v) w = c * D.ricci x v w := by
  obtain ⟨A, hA⟩ := ((hM04.tensor_calculus n M g D).2.1).1 x
  have heval : ∀ v w : TangentSpace (𝓡 n) x, D.ricci x v w = A ![v, w] := by
    intro v w
    simpa only [LeviCivitaData.ricciEvaluation, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hA ![v, w]
  rw [heval, heval]
  simpa only [smul_eq_mul, Matrix.vecCons] using A.cons_smul ![w] c v

theorem regularizedEulerResidual_square_transport (hM04 : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (squareReparameterizedCurve p.curve)
      (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)))) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (W : TangentSpace (𝓡 n) (p.curve (s ^ 2))) :
    regularizedEulerResidual F T (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) E s W =
      (4 * s ^ 2) * backwardEulerResidual F T p.curve (Set.Ioo τ₁ τ₂)
        (backwardExtensionOfSquare p E) (s ^ 2) W := by
  have hs0 := (sq_mem_backward_interior p.nonnegative hs).1.ne'
  let G := (F.metric (T - s ^ 2)).inner (p.curve (s ^ 2))
  let X := curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂) (s ^ 2)
  let A := pullbackCovariantDerivative F (fun r ↦ T - r) p.curve
    (curveVelocityWithin (n := n) p.curve (Set.Ioo τ₁ τ₂))
    (Set.Ioo τ₁ τ₂) (backwardExtensionOfSquare p E) (s ^ 2)
  have hmetric : G ((2 : ℝ) • X + (4 * s ^ 2) • A) W =
      2 * G X W + (4 * s ^ 2) * G A W := by
    rw [G.map_add, G.map_smul, G.map_smul]
    rfl
  unfold regularizedEulerResidual backwardEulerResidual
  rw [pullbackCovariantDerivative_square_transport p E hs, squarePath_velocityWithin p hs]
  rw [ricci_smul_left_of_curvatureTheory hM04]
  unfold scalarCurvatureDifferential squareReparameterizedCurve
  rw [hmetric]
  field_simp [hs0]
  ring

theorem isBackwardLGeodesic_of_regularizedEuler_extension {J : Set ℝ}
    {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (p : BackwardTimePath F T τ₁ τ₂)
    (E : ParametricAlongCurveExtensionOn (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (squareReparameterizedCurve p.curve)
      (curveVelocityWithin (n := n) (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))))
    (heq : ∀ s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
      regularizedLGeodesicEquation F T (squareReparameterizedCurve p.curve)
        (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) E s) :
    IsBackwardLGeodesic F T τ₁ τ₂ p := by
  refine ⟨backwardExtensionOfSquare p E, ?_⟩
  intro τ hτ W
  have hs := sqrt_mem_square_interior p.nonnegative hτ
  have hsq := Real.sq_sqrt hs.1.le
  have hr := regularizedEulerResidual_square_transport hM04 p E hs.2 W
  rw [heq _ hs.2 W, hsq] at hr
  exact (mul_eq_zero.mp hr.symm).resolve_left (mul_ne_zero (by norm_num) hs.1.ne')

end PoincareConjecture.M08

import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set VectorField

namespace PoincareConjecture

variable {n : ℕ}

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private noncomputable def koszulMap
    (B : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ) :
    E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ :=
  let flipL := (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toContinuousLinearMap
  (2⁻¹ : ℝ) • (B + (flipL.comp B).flip - flipL.comp B.flip)

private theorem koszulMap_apply
    (B : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ) (u v : E n) :
    koszulMap B u v = metricKoszulCovector B u v := by
  ext w
  rfl

private theorem contDiff_koszulMap :
    ContDiff ℝ ∞ (koszulMap (n := n)) := by
  unfold koszulMap
  have hf : ContDiff ℝ ∞ (fun B : E n →L[ℝ] E n →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) ℝ).toContinuousLinearMap.contDiff
  have hf' : ContDiff ℝ ∞
      (fun B : E n →L[ℝ] E n →L[ℝ] E n →L[ℝ] ℝ => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) (E n →L[ℝ] ℝ)).toContinuousLinearMap.contDiff
  fun_prop

namespace RiemannianMetric

variable (g : RiemannianMetric n (E n))

private noncomputable def christoffel (x : E n) : E n →L[ℝ] E n →L[ℝ] E n :=
  (ContinuousLinearMap.compL ℝ (E n) (E n →L[ℝ] ℝ) (E n)
    (g.euclideanCoefficients x).inverse).comp
      (koszulMap (fderiv ℝ g.euclideanCoefficients x))

private theorem christoffel_apply (x u v : E n) :
    christoffel g x u v = (g.euclideanCoefficients x).inverse
      (metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) u v) := by
  simp only [christoffel, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, koszulMap_apply]

private theorem contDiffAt_christoffel (x : E n) :
    ContDiffAt ℝ ∞ (christoffel g) x := by
  have hG := g.contDiffAt_euclideanCoefficients x
  have hginv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hi : ContDiffAt ℝ ∞ (fun y => (g.euclideanCoefficients y).inverse) x :=
    hginv.contDiffAt_map_inverse.comp x hG
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ g.euclideanCoefficients) x :=
    hG.fderiv_right (by simp)
  have hk := contDiff_koszulMap.contDiffAt.comp x hd
  unfold christoffel
  fun_prop

private theorem contDiff_euclideanCoefficients : ContDiff ℝ ∞ g.euclideanCoefficients :=
  contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients

private theorem fderiv_euclideanCoefficients_apply (x a b c : E n) :
    fderiv ℝ (fun y => g.inner y a b) x c =
      fderiv ℝ g.euclideanCoefficients x c a b := by
  have hG := ((g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp)).hasFDerivAt
  have h := (hG.clm_apply (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
  have hh := congrArg (fun L => L c) h.fderiv
  simp at hh
  convert! hh using 1

private theorem fderiv_euclideanCoefficients_symm (x a b c : E n) :
    fderiv ℝ g.euclideanCoefficients x c a b =
      fderiv ℝ g.euclideanCoefficients x c b a := by
  rw [← fderiv_euclideanCoefficients_apply, ← fderiv_euclideanCoefficients_apply]
  congr 2
  ext y
  exact g.symm y a b

private theorem inner_christoffel (x u v w : E n) :
    g.inner x (christoffel g x u v) w =
      (2⁻¹ : ℝ) * (fderiv ℝ g.euclideanCoefficients x u v w +
        fderiv ℝ g.euclideanCoefficients x v w u -
        fderiv ℝ g.euclideanCoefficients x w u v) := by
  rw [christoffel_apply]
  have hginv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  have hi := hginv.self_apply_inverse
    (metricKoszulCovector (fderiv ℝ g.euclideanCoefficients x) u v)
  have h := congrArg (fun L => L w) hi
  simp only [metricKoszulCovector, smul_apply, add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul] at h
  convert! h using 1

private theorem christoffel_symm (x u v : E n) :
    christoffel g x u v = christoffel g x v u := by
  have hginv : (g.euclideanCoefficients x).IsInvertible := by
    convert! g.inner_isInvertible x
  apply hginv.injective
  ext w
  change g.inner x (christoffel g x u v) w = g.inner x (christoffel g x v u) w
  rw [inner_christoffel, inner_christoffel]
  rw [fderiv_euclideanCoefficients_symm g x v w u,
    fderiv_euclideanCoefficients_symm g x w u v,
    fderiv_euclideanCoefficients_symm g x u v w]
  ring

private theorem inner_christoffel_add (x u v w : E n) :
    g.inner x (christoffel g x u v) w + g.inner x v (christoffel g x u w) =
      fderiv ℝ g.euclideanCoefficients x u v w := by
  rw [g.symm x v, inner_christoffel, inner_christoffel]
  rw [fderiv_euclideanCoefficients_symm g x w v u,
    fderiv_euclideanCoefficients_symm g x v u w,
    fderiv_euclideanCoefficients_symm g x u w v]
  ring

private theorem differentiableAt_of_field {Y : (x : E n) → TangentSpace (𝓡 n) x}
    {x : E n}
    (hY : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) (T% Y) x) :
    DifferentiableAt ℝ Y x := by
  rw [mdifferentiableAt_totalSpace] at hY
  apply mdifferentiableAt_iff_differentiableAt.mp
  simpa using hY.2

private theorem mdifferentiableAt_const_field (x v : E n) :
    MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y : E n => TotalSpace.mk' (E n) y (E := TangentSpace (𝓡 n)) v) x := by
  rw [mdifferentiableAt_totalSpace]
  exact ⟨mdifferentiableAt_id, by simpa using
    (mdifferentiableAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := v) (x := x))⟩

private noncomputable def euclideanConnection :
    CovariantDerivative (𝓡 n) (E n) (TangentSpace (𝓡 n) : E n → Type _) where
  toFun Y x := fderiv ℝ Y x + (christoffel g x).flip (Y x)
  isCovariantDerivativeOnUniv := {
    add := by
      intro Y Z x hY hZ hx
      have hY' := differentiableAt_of_field hY
      have hZ' := differentiableAt_of_field hZ
      change fderiv ℝ (Y + Z) x + (christoffel g x).flip (Y x + Z x) =
        (fderiv ℝ Y x + (christoffel g x).flip (Y x)) +
        (fderiv ℝ Z x + (christoffel g x).flip (Z x))
      simp only [fderiv_add hY' hZ', map_add]
      abel
    leibniz := by
      intro Y f x hY hf hx
      have hY' := differentiableAt_of_field hY
      have hf' := mdifferentiableAt_iff_differentiableAt.mp hf
      let S : E n → E n := Y
      simp only [mvfderiv, mfderiv_eq_fderiv]
      change fderiv ℝ (f • S) x + (christoffel g x).flip (f x • S x) =
        f x • (fderiv ℝ S x + (christoffel g x).flip (S x)) +
          (fderiv ℝ f x).smulRight (S x)
      rw [fderiv_smul hf' hY', map_smul, smul_add]
      abel }

private theorem euclideanConnection_const (x u v : E n) :
    euclideanConnection g (fun _ : E n => v) x u = christoffel g x u v := by
  simp [euclideanConnection]
  rfl

private theorem euclideanConnection_torsion : (euclideanConnection g).torsion = 0 := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  have h := (euclideanConnection g).torsion_apply
    (mdifferentiableAt_const_field x u) (mdifferentiableAt_const_field x v)
  change (euclideanConnection g).torsion x u v = 0
  rw [h, euclideanConnection_const, euclideanConnection_const, christoffel_symm g x u v]
  simp only [sub_self, mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
    lieBracketWithin, fderivWithin_univ, fderiv_const_apply]
  simp +instances

private theorem euclideanConnection_metricCompatible :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : E n → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (euclideanConnection g).IsMetricCompatible := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : E n → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold CovariantDerivative.IsMetricCompatible
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro u
  have h := (euclideanConnection g).derivMetricTensor_apply (X := fun _ => u) x
    (mdifferentiableAt_const_field x v) (mdifferentiableAt_const_field x w)
  change (euclideanConnection g).derivMetricTensor x v w u = 0
  rw [h]
  change (mvfderiv (𝓡 n) (fun y => g.inner y v w) x) u -
    g.inner x (euclideanConnection g (fun _ => v) x u) w -
    g.inner x v (euclideanConnection g (fun _ => w) x u) = 0
  rw [euclideanConnection_const, euclideanConnection_const]
  simp only [mvfderiv, mfderiv_eq_fderiv]
  simp +instances only [NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  change fderiv ℝ (fun y => g.inner y v w) x u -
    g.inner x (christoffel g x u v) w - g.inner x v (christoffel g x u w) = 0
  rw [fderiv_euclideanCoefficients_apply]
  linarith [inner_christoffel_add g x u v w]

private theorem euclideanConnection_smooth :
    CovariantDerivative.ContMDiffCovariantDerivative (euclideanConnection g) ∞ := by
  constructor
  constructor
  intro Y hY
  have hY' : ContDiff ℝ ∞ Y := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have h := (Bundle.contMDiffAt_totalSpace.mp ((contMDiffOn_univ.mp hY) x)).2
    apply contMDiffAt_iff_contDiffAt.mp
    simpa using h
  apply contMDiffOn_univ.mpr
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ Y) x := hY'.contDiffAt.fderiv_right (by simp)
  have hc := contDiffAt_christoffel g x
  have hf : ContDiff ℝ ∞
      (fun B : E n →L[ℝ] E n →L[ℝ] E n => B.flip) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (E n) (E n) (E n)).toContinuousLinearMap.contDiff
  have hh := hd.add ((hf.contDiffAt.comp x hc).clm_apply hY'.contDiffAt)
  convert! contMDiffAt_iff_contDiffAt.mpr hh using 1
  funext y
  apply ContinuousLinearMap.ext
  intro u
  simp [ContinuousLinearMap.inCoordinates, euclideanConnection,
    ContinuousLinearMap.one_def]
  rfl

noncomputable def euclideanLeviCivitaData
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) : LeviCivitaData g where
  connection := euclideanConnection g
  smooth := euclideanConnection_smooth g
  torsion_eq_zero := euclideanConnection_torsion g
  metricCompatible := euclideanConnection_metricCompatible g

end RiemannianMetric
end PoincareConjecture

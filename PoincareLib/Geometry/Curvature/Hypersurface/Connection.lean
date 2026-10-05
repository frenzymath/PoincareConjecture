import PoincareLib.Geometry.Riemannian.Connection.AlongCurve.Coefficients

/-!
# Covariant differentiation along a coordinate immersion

The ambient connection coefficients and the ordinary differential define
covariant differentiation of a vector field along a map. Metric compatibility
is derived from the compatibility of the ambient Levi-Civita connection.
Koszul's formula then proves normality of the actual second fundamental form
for a locally induced metric; no connection projection identity is assumed.
-/

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open PoincareMT
open scoped ContDiff Manifold Bundle Topology
open Filter

namespace Poincare.Geometry.Curvature.Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

/-- The ambient covariant derivative of a vector field along a map, in
coordinates. The connection coefficient is that of the actual ambient metric. -/
def covariantDerivativeAlongMap (D : LeviCivitaData g)
    (F W : E → EuclideanSpace ℝ (Fin n)) (x : E) (v : E) :
    EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ W x v + D.connectionCoefficient (F x) (fderiv ℝ F x v) (W x)

/-- Differentiating the ambient metric pairing of two fields along a map
obeys the covariant product rule. -/
theorem covariantDerivativeAlongMap_metricCompatible (D : LeviCivitaData g)
    {F V W : E → EuclideanSpace ℝ (Fin n)} {x : E}
    (hF : DifferentiableAt ℝ F x) (hV : DifferentiableAt ℝ V x)
    (hW : DifferentiableAt ℝ W x) (v : E) :
    fderiv ℝ (fun y => g.inner (F y) (V y) (W y)) x v =
      g.inner (F x) (covariantDerivativeAlongMap D F V x v) (W x) +
        g.inner (F x) (V x) (covariantDerivativeAlongMap D F W x v) := by
  have hG : DifferentiableAt ℝ (fun y => g.euclideanCoefficients (F y)) x :=
    ((g.contDiffAt_euclideanCoefficients (F x)).differentiableAt (by simp)).comp x hF
  change fderiv ℝ (fun y => g.euclideanCoefficients (F y) (V y) (W y)) x v =
    g.euclideanCoefficients (F x) (covariantDerivativeAlongMap D F V x v) (W x) +
      g.euclideanCoefficients (F x) (V x) (covariantDerivativeAlongMap D F W x v)
  rw [fderiv_clm_apply (hG.clm_apply hV) hW, fderiv_clm_apply hG hV,
    fderiv_fun_comp x ((g.contDiffAt_euclideanCoefficients (F x)).differentiableAt
      (by simp)) hF]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  have hcompat : fderiv ℝ g.euclideanCoefficients (F x) (fderiv ℝ F x v)
      (V x) (W x) =
      g.euclideanCoefficients (F x)
        (D.connectionCoefficient (F x) (fderiv ℝ F x v) (V x)) (W x) +
      g.euclideanCoefficients (F x) (V x)
        (D.connectionCoefficient (F x) (fderiv ℝ F x v) (W x)) :=
    D.connectionCoefficient_metricCompatible (F x) (fderiv ℝ F x v) (V x) (W x)
  rw [hcompat]
  simp only [covariantDerivativeAlongMap, map_add, add_apply]
  abel

/-- The coefficients of a torsion-free connection are symmetric in the
coordinate directions. -/
theorem connectionCoefficient_symm (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    D.connectionCoefficient x u v = D.connectionCoefficient x v u := by
  have hc (w : EuclideanSpace ℝ (Fin n)) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
        (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
          (E := TangentSpace (𝓡 n)) w) x := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by simpa using
      (mdifferentiableAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := w) (x := x))⟩
  have ht := D.covariantDerivativeOnFields_sub_swap (hc u) (hc v)
  change D.connectionCoefficient x u v - D.connectionCoefficient x v u = _ at ht
  simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin, fderivWithin_univ, fderiv_const_apply, zero_apply,
    sub_self] at ht
  exact sub_eq_zero.mp ht

/-- The covariant second derivative of the immersion on constant coordinate
vectors, using the actual ambient connection. -/
def covariantHessianMap (D : LeviCivitaData g)
    (F : E → EuclideanSpace ℝ (Fin n)) (x u v : E) :
    EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (fderiv ℝ F) x u v +
    D.connectionCoefficient (F x) (fderiv ℝ F x u) (fderiv ℝ F x v)

/-- Torsion freeness of the ambient connection and Hessian symmetry imply
symmetry of the covariant second derivative. -/
theorem covariantHessianMap_symm (D : LeviCivitaData g)
    {F : E → EuclideanSpace ℝ (Fin n)} {x : E}
    (hF : ContDiffAt ℝ ∞ F x) (u v : E) :
    covariantHessianMap D F x u v = covariantHessianMap D F x v u := by
  have hs := hF.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  rw [covariantHessianMap, covariantHessianMap, hs u v, connectionCoefficient_symm]

/-- Differentiating the image of a constant source field computes the
covariant second derivative of the map. -/
theorem covariantDerivativeAlongMap_fderiv_const (D : LeviCivitaData g)
    {F : E → EuclideanSpace ℝ (Fin n)} {x : E}
    (hF : ContDiffAt ℝ ∞ F x) (u v : E) :
    covariantDerivativeAlongMap D F (fun y => fderiv ℝ F y v) x u =
      covariantHessianMap D F x u v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  simp only [covariantDerivativeAlongMap, covariantHessianMap]
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

variable {m : ℕ} {h : RiemannianMetric m (EuclideanSpace ℝ (Fin m))}

/-- The second fundamental form is the difference between ambient covariant
second differentiation and the lifted source connection. -/
def secondFundamentalForm (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n))
    (x u v : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin n) :=
  covariantHessianMap D F x u v - fderiv ℝ F x (D'.connectionCoefficient x u v)

/-- The pointwise second fundamental form agrees with the difference of the
actual ambient and intrinsic derivatives on every differentiable field. -/
theorem secondFundamentalForm_eq_covariantDerivativeAlongMap
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {Y : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin m)} (hF : ContDiffAt ℝ ∞ F x)
    (hY : DifferentiableAt ℝ Y x) (u : EuclideanSpace ℝ (Fin m)) :
    secondFundamentalForm D D' F x u (Y x) =
      covariantDerivativeAlongMap D F (fun y => fderiv ℝ F y (Y y)) x u -
        fderiv ℝ F x (D'.connection Y x u) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  rw [covariantDerivativeAlongMap, fderiv_clm_apply hd hY,
    D'.connection_eq_fderiv_add hY]
  simp only [secondFundamentalForm, covariantHessianMap, add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_add,
    LeviCivitaData.connectionCoefficient_apply]
  abel

/-- The second fundamental form is symmetric because both actual connections
are torsion free. -/
theorem secondFundamentalForm_symm (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (hF : ContDiffAt ℝ ∞ F x)
    (u v : EuclideanSpace ℝ (Fin m)) :
    secondFundamentalForm D D' F x u v = secondFundamentalForm D D' F x v u := by
  rw [secondFundamentalForm, secondFundamentalForm, covariantHessianMap_symm D hF,
    connectionCoefficient_symm D']

/-- Koszul's formula proves that the second fundamental form is orthogonal
to the tangent image for the actual induced metric. -/
theorem secondFundamentalForm_normal (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin m)} (hF : ContDiffAt ℝ ∞ F x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u v w : EuclideanSpace ℝ (Fin m)) :
    g.inner (F x) (secondFundamentalForm D D' F x u v) (fderiv ℝ F x w) = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hp (a b c : EuclideanSpace ℝ (Fin m)) :
      fderiv ℝ (fun y => h.inner y b c) x a =
        g.inner (F x) (covariantHessianMap D F x a b) (fderiv ℝ F x c) +
        g.inner (F x) (fderiv ℝ F x b) (covariantHessianMap D F x a c) := by
    have he : (fun y => h.inner y b c) =ᶠ[𝓝 x]
        (fun y => g.inner (F y) (fderiv ℝ F y b) (fderiv ℝ F y c)) :=
      hmetric.mono fun y hy => hy b c
    rw [he.fderiv_eq, covariantDerivativeAlongMap_metricCompatible D
      (hF.differentiableAt (by simp)) (hd.clm_apply (differentiableAt_const b))
      (hd.clm_apply (differentiableAt_const c)),
      covariantDerivativeAlongMap_fderiv_const D hF,
      covariantDerivativeAlongMap_fderiv_const D hF]
  have hk := D'.inner_connection_const x u v w
  rw [hp, hp, hp, hmetric.self_of_nhds] at hk
  change 2 * g.inner (F x)
    (fderiv ℝ F x (D'.connectionCoefficient x u v)) (fderiv ℝ F x w) = _ at hk
  rw [covariantHessianMap_symm D hF v u, covariantHessianMap_symm D hF w v,
    covariantHessianMap_symm D hF w u] at hk
  rw [g.symm (F x) (fderiv ℝ F x v), g.symm (F x) (fderiv ℝ F x w),
    g.symm (F x) (fderiv ℝ F x u)] at hk
  unfold secondFundamentalForm
  simp only [map_sub, sub_apply]
  linarith

end Poincare.Geometry.Curvature.Hypersurface

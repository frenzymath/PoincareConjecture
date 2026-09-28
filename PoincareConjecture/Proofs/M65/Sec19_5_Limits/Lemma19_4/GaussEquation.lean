import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussMapCurvature









noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M65Gauss

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

variable {m n : ℕ} {g : RiemannianMetric n (E n)} {h : RiemannianMetric m (E m)}



theorem contDiffAt_secondFundamentalForm (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E n} {x : E m} (hF : ContDiffAt ℝ ∞ F x) (u v : E m) :
    ContDiffAt ℝ ∞ (fun y => secondFundamentalForm D D' F y u v) x := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ F) x := hF.fderiv_right (by simp)
  have hdd : ContDiffAt ℝ ∞ (fderiv ℝ (fderiv ℝ F)) x := hd.fderiv_right (by simp)
  have hΓ := (contDiff_connectionCoefficient D).contDiffAt.comp x hF
  have hΓ' := (contDiff_connectionCoefficient D').contDiffAt (x := x)
  exact (((hdd.clm_apply contDiffAt_const).clm_apply contDiffAt_const).add
    ((hΓ.clm_apply (hd.clm_apply contDiffAt_const)).clm_apply
      (hd.clm_apply contDiffAt_const))).sub
    (hd.clm_apply ((hΓ'.clm_apply contDiffAt_const).clm_apply contDiffAt_const))



private theorem covariantDerivativeAlongMap_congr (D : LeviCivitaData g)
    (F : E m → E n) {V W : E m → E n} {x : E m}
    (hVW : V =ᶠ[𝓝 x] W) (u : E m) :
    covariantDerivativeAlongMap D F V x u = covariantDerivativeAlongMap D F W x u := by
  unfold covariantDerivativeAlongMap
  rw [hVW.fderiv_eq, hVW.self_of_nhds]



private theorem covariantDerivativeAlongMap_add (D : LeviCivitaData g)
    (F : E m → E n) {V W : E m → E n} {x : E m}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) (u : E m) :
    covariantDerivativeAlongMap D F (fun y => V y + W y) x u =
      covariantDerivativeAlongMap D F V x u + covariantDerivativeAlongMap D F W x u := by
  simp only [covariantDerivativeAlongMap, fderiv_fun_add hV hW, add_apply, map_add]
  abel



theorem secondFundamentalForm_covariantDerivative_inner
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E n} {x : E m} (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u v z w : E m) :
    g.inner (F x)
        (covariantDerivativeAlongMap D F (fun y => secondFundamentalForm D D' F y v z) x u)
        (fderiv ℝ F x w) =
      -g.inner (F x) (secondFundamentalForm D D' F x v z)
        (secondFundamentalForm D D' F x u w) := by
  have hFx := hF.self_of_nhds
  have hB := contDiffAt_secondFundamentalForm D D' hFx v z
  have hT : ContDiffAt ℝ ∞ (fun y => fderiv ℝ F y w) x :=
    (hFx.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hzero : (fun y => g.inner (F y) (secondFundamentalForm D D' F y v z)
      (fderiv ℝ F y w)) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hmetric.eventually_nhds, hF] with y hy hFy
    exact secondFundamentalForm_normal D D' hFy hy v z w
  have hprod := covariantDerivativeAlongMap_metricCompatible D
    (hFx.differentiableAt (by simp)) (hB.differentiableAt (by simp))
    (hT.differentiableAt (by simp)) u
  rw [hzero.fderiv_eq, fderiv_const_apply, zero_apply,
    covariantDerivativeAlongMap_fderiv_const D hFx] at hprod
  have hn := secondFundamentalForm_normal D D' hFx hmetric
    v z (connectionCoefficient D' x u w)
  change g.inner (F x)
      (covariantDerivativeAlongMap D F (fun y => secondFundamentalForm D D' F y v z) x u)
      (fderiv ℝ F x w) =
    -g.inner (F x) (secondFundamentalForm D D' F x v z)
      (covariantHessianMap D F x u w - fderiv ℝ F x (connectionCoefficient D' x u w))
  rw [map_sub, hn, sub_zero]
  linarith



private theorem covariantDerivativeAlongMap_lift_inner
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E n} {Y : E m → E m} {x : E m} (hF : ContDiffAt ℝ ∞ F x)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (hY : DifferentiableAt ℝ Y x) (u w : E m) :
    g.inner (F x)
      (covariantDerivativeAlongMap D F (fun y => fderiv ℝ F y (Y y)) x u)
      (fderiv ℝ F x w) = h.inner x (D'.connection Y x u) w := by
  have hn := secondFundamentalForm_normal D D' hF hmetric u (Y x) w
  rw [secondFundamentalForm_eq_covariantDerivativeAlongMap D D' hF hY,
    map_sub, sub_apply, ← hmetric.self_of_nhds] at hn
  linarith



private theorem iterated_covariantDerivativeAlongMap_inner
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E n} {x : E m} (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u v z w : E m) :
    g.inner (F x)
        (covariantDerivativeAlongMap D F
          (fun y => covariantDerivativeAlongMap D F (fun q => fderiv ℝ F q z) y v) x u)
        (fderiv ℝ F x w) =
      h.inner x (D'.connection (fun y => connectionCoefficient D' y v z) x u) w -
        g.inner (F x) (secondFundamentalForm D D' F x v z)
          (secondFundamentalForm D D' F x u w) := by
  have hFx := hF.self_of_nhds
  have hC : ContDiff ℝ ∞ (fun y => connectionCoefficient D' y v z) :=
    ((contDiff_connectionCoefficient D').clm_apply contDiff_const).clm_apply contDiff_const
  have hT : ContDiffAt ℝ ∞ (fun y => fderiv ℝ F y (connectionCoefficient D' y v z)) x :=
    (hFx.fderiv_right (by simp)).clm_apply hC.contDiffAt
  have hB := contDiffAt_secondFundamentalForm D D' hFx v z
  have he : (fun y => covariantDerivativeAlongMap D F (fun q => fderiv ℝ F q z) y v) =ᶠ[𝓝 x]
      fun y => fderiv ℝ F y (connectionCoefficient D' y v z) +
        secondFundamentalForm D D' F y v z := by
    filter_upwards [hF] with y hy
    rw [covariantDerivativeAlongMap_fderiv_const D hy]
    unfold secondFundamentalForm
    abel
  rw [covariantDerivativeAlongMap_congr D F he, covariantDerivativeAlongMap_add D F
    (hT.differentiableAt (by simp)) (hB.differentiableAt (by simp)),
    map_add, add_apply, covariantDerivativeAlongMap_lift_inner D D' hFx hmetric
      (hC.differentiable (by simp) x),
    secondFundamentalForm_covariantDerivative_inner D D' hF hmetric]
  rfl



theorem gauss_curvatureTensor (D : LeviCivitaData g) (D' : LeviCivitaData h)
    {F : E m → E n} {x : E m} (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b, h.inner y a b =
      g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u v w z : E m) :
    D'.curvatureTensor x u v w z =
      D.curvatureTensor (F x) (fderiv ℝ F x u) (fderiv ℝ F x v)
        (fderiv ℝ F x w) (fderiv ℝ F x z) +
      g.inner (F x) (secondFundamentalForm D D' F x u w)
        (secondFundamentalForm D D' F x v z) -
      g.inner (F x) (secondFundamentalForm D D' F x u z)
        (secondFundamentalForm D D' F x v w) := by
  have hC (a b : E m) : ContDiff ℝ ∞ (fun y => connectionCoefficient D' y a b) :=
    ((contDiff_connectionCoefficient D').clm_apply contDiff_const).clm_apply contDiff_const
  have hs : D'.curvature x u v z =
      D'.connection (fun y => connectionCoefficient D' y v z) x u -
        D'.connection (fun y => connectionCoefficient D' y u z) x v := by
    rw [D'.connection_eq_fderiv_add ((hC v z).differentiable (by simp) x),
      D'.connection_eq_fderiv_add ((hC u z).differentiable (by simp) x)]
    exact D'.curvature_eq_euclideanConnection x u v z
  have hT : ContDiffAt ℝ ∞ (fun y => fderiv ℝ F y z) x :=
    (hF.self_of_nhds.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hc := congrArg (fun a => g.inner (F x) a (fderiv ℝ F x w))
    (covariantDerivativeAlongMap_curvature D hF.self_of_nhds hT u v)
  rw [map_sub, sub_apply, iterated_covariantDerivativeAlongMap_inner D D' hF hmetric,
    iterated_covariantDerivativeAlongMap_inner D D' hF hmetric] at hc
  change h.inner x (D'.curvature x u v z) w =
    g.inner (F x) (D.curvature (F x) (fderiv ℝ F x u) (fderiv ℝ F x v)
      (fderiv ℝ F x z)) (fderiv ℝ F x w) + _ - _
  rw [hs, map_sub, sub_apply]
  rw [g.symm (F x) (secondFundamentalForm D D' F x u w)]
  linarith

end PoincareConjecture.M65Gauss

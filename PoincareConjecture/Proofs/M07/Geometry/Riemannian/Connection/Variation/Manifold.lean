import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Transition.Hessian
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Coordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Manifold

namespace PoincareConjecture.ConnectionVariation

open CoordinateExponential CoordinateTransition

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem covDerivAlong_congr_base
    (A : E → E →L[ℝ] E →L[ℝ] E) {u u' : P → E} (V : P → E)
    {p : P} (h : u =ᶠ[𝓝 p] u') (d : P) :
    covDerivAlong A u V d p = covDerivAlong A u' V d p := by
  simp only [covDerivAlong, h.fderiv_eq, h.eq_of_nhds]


theorem covDerivAlong_change_coordinates
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {u V : P → E} {p : P}
    (hB : DifferentiableAt ℝ B (u p)) (hC : DifferentiableAt ℝ C (f (u p)))
    (hBinv : (B (u p)).IsInvertible) (hCinv : (C (f (u p))).IsInvertible)
    (hBsymm : ∀ᶠ y in 𝓝 (u p), ∀ a b, B y a b = B y b a)
    (hCsymm : ∀ᶠ y in 𝓝 (f (u p)), ∀ a b, C y a b = C y b a)
    (hf : ContDiffAt ℝ ∞ f (u p))
    (hsurj : Function.Surjective (fderiv ℝ f (u p)))
    (hmetric : ∀ᶠ y in 𝓝 (u p), ∀ a b,
      B y a b = C (f y) (fderiv ℝ f y a) (fderiv ℝ f y b))
    (hu : DifferentiableAt ℝ u p) (hV : DifferentiableAt ℝ V p) (d : P) :
    covDerivAlong (christoffelBilinear C) (f ∘ u)
        (fun q => fderiv ℝ f (u q) (V q)) d p =
      fderiv ℝ f (u p) (covDerivAlong (christoffelBilinear B) u V d p) := by
  have hDf := (hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hfield := (hDf.hasFDerivAt.comp p hu.hasFDerivAt).clm_apply hV.hasFDerivAt
  simp only [Function.comp_def] at hfield
  have hposition := (hf.differentiableAt (by simp)).hasFDerivAt.comp p hu.hasFDerivAt
  rw [covDerivAlong, hfield.fderiv, hposition.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Function.comp_apply]
  rw [fderiv_fderiv_eq_christoffel hB hC hBinv hCinv hBsymm hCsymm hf hsurj hmetric]
  simp only [covDerivAlong, map_add]
  abel


theorem covDerivAlong_change_coordinatesOn [FiniteDimensional ℝ E]
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {U W : Set E}
    (hU : IsOpen U) (hW : IsOpen W)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C W)
    (hf : ContDiffOn ℝ ∞ f U) (hmap : MapsTo f U W)
    (hBinv : ∀ x ∈ U, (B x).IsInvertible)
    (hCinv : ∀ y ∈ W, (C y).IsInvertible)
    (hBsymm : ∀ x ∈ U, ∀ a b, B x a b = B x b a)
    (hCsymm : ∀ y ∈ W, ∀ a b, C y a b = C y b a)
    (hmetric : ∀ x ∈ U, ∀ a b,
      B x a b = C (f x) (fderiv ℝ f x a) (fderiv ℝ f x b))
    {u V : P → E} {p : P} (hp : u p ∈ U)
    (hu : DifferentiableAt ℝ u p) (hV : DifferentiableAt ℝ V p) (d : P) :
    covDerivAlong (christoffelBilinear C) (f ∘ u)
        (fun q => fderiv ℝ f (u q) (V q)) d p =
      fderiv ℝ f (u p) (covDerivAlong (christoffelBilinear B) u V d p) := by
  exact covDerivAlong_change_coordinates
    ((hB.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp))
    ((hC.contDiffAt (hW.mem_nhds (hmap hp))).differentiableAt (by simp))
    (hBinv _ hp) (hCinv _ (hmap hp))
    (Filter.mem_of_superset (hU.mem_nhds hp) hBsymm)
    (Filter.mem_of_superset (hW.mem_nhds (hmap hp)) hCsymm)
    (hf.contDiffAt (hU.mem_nhds hp))
    (surjective_of_pullback_isInvertible (hBinv _ hp) (hmetric _ hp))
    (Filter.mem_of_superset (hU.mem_nhds hp) hmetric) hu hV d


theorem covDerivAlong_covDerivAlong_change_coordinatesOn
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {U W : Set E}
    (hU : IsOpen U) (hW : IsOpen W)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C W)
    (hf : ContDiffOn ℝ ∞ f U) (hmap : MapsTo f U W)
    (hBinv : ∀ x ∈ U, (B x).IsInvertible)
    (hCinv : ∀ y ∈ W, (C y).IsInvertible)
    (hBsymm : ∀ x ∈ U, ∀ a b, B x a b = B x b a)
    (hCsymm : ∀ y ∈ W, ∀ a b, C y a b = C y b a)
    (hmetric : ∀ x ∈ U, ∀ a b,
      B x a b = C (f x) (fderiv ℝ f x a) (fderiv ℝ f x b))
    {u V : P → E} {p : P} (hp : u p ∈ U)
    (hu : ContDiffAt ℝ ∞ u p) (hV : ContDiffAt ℝ ∞ V p) (d e : P) :
    covDerivAlong (christoffelBilinear C) (f ∘ u)
        (covDerivAlong (christoffelBilinear C) (f ∘ u)
          (fun q => fderiv ℝ f (u q) (V q)) d) e p =
      fderiv ℝ f (u p)
        (covDerivAlong (christoffelBilinear B) u
          (covDerivAlong (christoffelBilinear B) u V d) e p) := by
  have heq : covDerivAlong (christoffelBilinear C) (f ∘ u)
      (fun q => fderiv ℝ f (u q) (V q)) d =ᶠ[𝓝 p]
      (fun q => fderiv ℝ f (u q) (covDerivAlong (christoffelBilinear B) u V d q)) := by
    filter_upwards [hu.continuousAt.preimage_mem_nhds (hU.mem_nhds hp),
      (hu.of_le (show (1 : ℕ∞ω) ≤ ∞ by norm_cast)).eventually (by simp),
      (hV.of_le (show (1 : ℕ∞ω) ≤ ∞ by norm_cast)).eventually (by simp)]
      with q hq huq hVq
    exact covDerivAlong_change_coordinatesOn hU hW hB hC hf hmap
      hBinv hCinv hBsymm hCsymm hmetric hq
      (huq.differentiableAt (by simp)) (hVq.differentiableAt (by simp)) d
  rw [covDerivAlong_congr _ _ heq]
  exact covDerivAlong_change_coordinatesOn hU hW hB hC hf hmap
    hBinv hCinv hBsymm hCsymm hmetric hp (hu.differentiableAt (by simp))
    ((contDiffAt_covDerivAlong
      (contDiffAt_christoffelBilinear (hB.contDiffAt (hU.mem_nhds hp)) (hBinv _ hp))
      hu hV d).differentiableAt (by simp)) e

section Manifold

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem coordinateCurvature_congr_germ
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (h : B =ᶠ[𝓝 x] C) (u v w : E) :
    coordinateCurvature B x u v w = coordinateCurvature C x u v w := by
  have hΓ : ∀ᶠ y in 𝓝 x, ∀ a b,
      coordinateChristoffel B y a b = coordinateChristoffel C y a b := by
    filter_upwards [h.eventually_nhds] with y hy a b
    have hBC : B =ᶠ[𝓝 y] C := hy
    simp only [coordinateChristoffel, hBC.eq_of_nhds, hBC.fderiv_eq]
  have hΓ' (a b : E) : (fun y => coordinateChristoffel B y a b) =ᶠ[𝓝 x]
      (fun y => coordinateChristoffel C y a b) := hΓ.mono fun _ hy => hy a b
  simp only [coordinateCurvature, (hΓ' v w).fderiv_eq, (hΓ' u w).fderiv_eq,
    hΓ.self_of_nhds]



theorem coordinateCurvature_in_chart (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (a : M) {z : M}
    (hz : z ∈ (extChartAt (𝓡 n) a).source)
    (u v w : TangentSpace (𝓡 n) z) :
    coordinateCurvature (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a z)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) z u)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) z v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) z w) =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) z (D.curvature z u v w) := by
  let c := extChartAt (𝓡 n) a
  let p := c z
  have hp : p ∈ c.target := c.map_source hz
  have hc (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) a hy).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  have hi (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
      (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  obtain ⟨gE, DE, V, hVo, hpV, _, hE⟩ :=
    RiemannianMetric.exists_local_realization (isOpen_extChartAt_target a) hp
      (g.pullbackCoefficients c.symm) (g.contDiffOn_chartCoefficients a)
      (fun y _ b d => g.symm _ _ _)
      (fun y hy b hb => by
        apply g.pos (c.symm y)
        intro hzero
        apply hb
        apply (hi y hy).injective
        rw [map_zero]
        exact hzero)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 p] g.pullbackCoefficients c.symm := by
    filter_upwards [hVo.mem_nhds hpV] with y hy
    exact hE y hy
  have hinv : ∀ᶠ y in 𝓝 p, (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible :=
    Filter.mem_of_superset (extChartAt_target_mem_nhds' hp) hi
  have hmetric : ∀ᶠ y in 𝓝 p, ∀ b d : EuclideanSpace ℝ (Fin n),
      gE.inner y b d = g.inner (c.symm y)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y b)
        (mfderiv (𝓡 n) (𝓡 n) c.symm y d) := by
    filter_upwards [heq] with y hy b d
    exact congrArg (fun B => B b d) hy
  have hid := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n) hz
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hid
  have hid' (b : TangentSpace (𝓡 n) z) :
      mfderiv (𝓡 n) (𝓡 n) c.symm p (mfderiv (𝓡 n) (𝓡 n) c z b) = b :=
    congrArg (fun L => L b) hid
  rw [← coordinateCurvature_congr_germ heq,
    coordinateCurvature_eq_retained DE,
    DE.curvature_eq_pullback_euclidean D (hc p hp) hinv hmetric]
  apply (hi p hp).injective
  rw [(hi p hp).self_apply_inverse, hid', hid', hid', hid']
  exact congrArg (fun y => D.curvature y u v w) (c.left_inv hz)




noncomputable def manifoldCovDerivAlong (g : RiemannianMetric n M)
    (u : P → M) (V : (q : P) → TangentSpace (𝓡 n) (u q)) (d p : P) :
    TangentSpace (𝓡 n) (u p) :=
  let c := extChartAt (𝓡 n) (u p)
  (mfderiv (𝓡 n) (𝓡 n) c (u p)).inverse
    (covDerivAlong (christoffelBilinear (g.pullbackCoefficients c.symm))
      (c ∘ u)
      (fun q => mfderiv (𝓡 n) (𝓡 n) c (u q) (V q)) d p)

private theorem smooth_chart_transition (a b : M) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) a).target)
    (hb : (extChartAt (𝓡 n) a).symm x ∈ (extChartAt (𝓡 n) b).source) :
    ContDiffAt ℝ ∞ ((extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm) x := by
  apply contMDiffAt_iff_contDiffAt.mp
  exact (contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hb)).comp x
    ((contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds hx))


theorem chart_transition_tangent (a b : M) {z : M}
    (ha : z ∈ (extChartAt (𝓡 n) a).source)
    (hb : z ∈ (extChartAt (𝓡 n) b).source) (v : TangentSpace (𝓡 n) z) :
    fderiv ℝ ((extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm)
        (extChartAt (𝓡 n) a z) (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) z v) =
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b) z v := by
  have hleft := (extChartAt (𝓡 n) a).left_inv ha
  have hd := mfderiv_comp (extChartAt (𝓡 n) a z)
    (mdifferentiableAt_extChartAt (x := b)
      (by simpa only [hleft, extChartAt_source] using hb))
    (((contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) a).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds
        ((extChartAt (𝓡 n) a).map_source ha))).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hd
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n) ha
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
  have hv := congrArg (fun L => L v) hi
  change mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm
    (extChartAt (𝓡 n) a z) (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) z v) = v at hv
  erw [hd, ContinuousLinearMap.comp_apply, hv]
  exact congrArg (fun y => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b) y v) hleft

private theorem chart_metric_transition (g : RiemannianMetric n M) (a b : M)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) a).target)
    (hb : (extChartAt (𝓡 n) a).symm x ∈ (extChartAt (𝓡 n) b).source)
    (v w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients (extChartAt (𝓡 n) a).symm x v w =
      g.pullbackCoefficients (extChartAt (𝓡 n) b).symm
        (((extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm) x)
        (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm) x v)
        (fderiv ℝ ((extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm) x w) := by
  let f := (extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm
  have ha := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) a).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds hx)
  have hf := smooth_chart_transition a b hx hb
  have hb' := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 n) b).mem_nhds
      ((extChartAt (𝓡 n) b).map_source hb))
  have heq : ((extChartAt (𝓡 n) b).symm ∘ f) =ᶠ[𝓝 x]
      (extChartAt (𝓡 n) a).symm := by
    filter_upwards [ha.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source b).mem_nhds hb)] with y hy
    exact (extChartAt (𝓡 n) b).left_inv hy
  have hd := mfderiv_comp x (hb'.mdifferentiableAt (by simp))
    (hf.differentiableAt (by simp)).mdifferentiableAt
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hd
  have hdv := congrArg (fun L => L v) hd
  have hdw := congrArg (fun L => L w) hd
  change g.inner ((extChartAt (𝓡 n) a).symm x)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm x v)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a).symm x w) = _
  erw [hdv, hdw]
  exact congrArg (fun y => g.inner y
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm (f x) (fderiv ℝ f x v))
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) b).symm (f x) (fderiv ℝ f x w)))
    heq.self_of_nhds.symm

set_option maxHeartbeats 2000000 in


theorem covDerivAlong_chart_change (g : RiemannianMetric n M) (a b : M)
    {u V : P → EuclideanSpace ℝ (Fin n)} {p : P}
    (ha : u p ∈ (extChartAt (𝓡 n) a).target)
    (hb : (extChartAt (𝓡 n) a).symm (u p) ∈ (extChartAt (𝓡 n) b).source)
    (hu : DifferentiableAt ℝ u p) (hV : DifferentiableAt ℝ V p) (d : P) :
    let f := (extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm
    covDerivAlong (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) b).symm))
        (f ∘ u) (fun q => fderiv ℝ f (u q) (V q)) d p =
      fderiv ℝ f (u p)
        (covDerivAlong (christoffelBilinear
          (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm)) u V d p) := by
  let f := (extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm
  have hmetric : ∀ᶠ x in 𝓝 (u p), ∀ v w,
      g.pullbackCoefficients (extChartAt (𝓡 n) a).symm x v w =
        g.pullbackCoefficients (extChartAt (𝓡 n) b).symm (f x)
          (fderiv ℝ f x v) (fderiv ℝ f x w) := by
    have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) a).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds ha)
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds ha,
      hc.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source b).mem_nhds hb)]
      with x hxa hxb v w
    exact chart_metric_transition g a b hxa hxb v w
  have hb' := (extChartAt (𝓡 n) b).map_source hb
  exact covDerivAlong_change_coordinates
    (((g.contDiffOn_chartCoefficients a).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) a).mem_nhds ha)).differentiableAt (by simp))
    (((g.contDiffOn_chartCoefficients b).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) b).mem_nhds hb')).differentiableAt (by simp))
    (g.isInvertible_chartCoefficients a ha) (g.isInvertible_chartCoefficients b hb')
    (Eventually.of_forall fun _ v w => g.symm _ _ _)
    (Eventually.of_forall fun _ v w => g.symm _ _ _)
    (smooth_chart_transition a b ha hb)
    (surjective_of_pullback_isInvertible (g.isInvertible_chartCoefficients a ha)
      hmetric.self_of_nhds) hmetric hu hV d



theorem manifoldCovDerivAlong_in_chart (g : RiemannianMetric n M) (a : M)
    {u : P → M} {V : (q : P) → TangentSpace (𝓡 n) (u q)} {p : P}
    (ha : u p ∈ (extChartAt (𝓡 n) a).source) (hu : ContinuousAt u p)
    (hcu : DifferentiableAt ℝ ((extChartAt (𝓡 n) a) ∘ u) p)
    (hV : DifferentiableAt ℝ
      (fun q => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (u q) (V q)) p)
    (d : P) :
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (u p)
        (manifoldCovDerivAlong g u V d p) =
      covDerivAlong (christoffelBilinear
        (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm))
        ((extChartAt (𝓡 n) a) ∘ u)
        (fun q => mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) a) (u q) (V q)) d p := by
  let b := u p
  let ca := extChartAt (𝓡 n) a
  let cb := extChartAt (𝓡 n) b
  let f := cb ∘ ca.symm
  let ua := ca ∘ u
  let Va := fun q => mfderiv (𝓡 n) (𝓡 n) ca (u q) (V q)
  have hb : u p ∈ cb.source := mem_extChartAt_source (u p)
  have hnear : ∀ᶠ q in 𝓝 p, u q ∈ ca.source ∧ u q ∈ cb.source :=
    hu.preimage_mem_nhds (inter_mem
      ((isOpen_extChartAt_source a).mem_nhds ha)
      ((isOpen_extChartAt_source b).mem_nhds hb))
  have hub : cb ∘ u =ᶠ[𝓝 p] f ∘ ua := by
    filter_upwards [hnear] with q hq
    simp only [f, ua, Function.comp_apply, ca.left_inv hq.1]
  have hVb : (fun q => mfderiv (𝓡 n) (𝓡 n) cb (u q) (V q)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ f (ua q) (Va q)) := by
    filter_upwards [hnear] with q hq
    exact (chart_transition_tangent a b hq.1 hq.2 (V q)).symm
  have hca : ca (u p) ∈ ca.target := ca.map_source ha
  have hcb : ca.symm (ca (u p)) ∈ cb.source := by
    simpa only [ca.left_inv ha] using hb
  have htrans := covDerivAlong_chart_change (P := P) g a b hca hcb hcu hV d
  change covDerivAlong (christoffelBilinear (g.pullbackCoefficients cb.symm))
      (f ∘ ua) (fun q => fderiv ℝ f (ua q) (Va q)) d p =
      fderiv ℝ f (ua p)
        (covDerivAlong (christoffelBilinear (g.pullbackCoefficients ca.symm)) ua Va d p)
    at htrans
  have hvalue := chart_transition_tangent a b ha hb
    ((mfderiv (𝓡 n) (𝓡 n) ca (u p)).inverse
      (covDerivAlong (christoffelBilinear (g.pullbackCoefficients ca.symm)) ua Va d p))
  rw [(isInvertible_mfderiv_extChartAt ha).self_apply_inverse] at hvalue
  have heq : manifoldCovDerivAlong g u V d p =
      (mfderiv (𝓡 n) (𝓡 n) ca (u p)).inverse
        (covDerivAlong (christoffelBilinear (g.pullbackCoefficients ca.symm)) ua Va d p) := by
    apply (isInvertible_mfderiv_extChartAt hb).injective
    change mfderiv (𝓡 n) (𝓡 n) cb (u p)
      ((mfderiv (𝓡 n) (𝓡 n) cb (u p)).inverse _) = _
    rw [(isInvertible_mfderiv_extChartAt hb).self_apply_inverse]
    change covDerivAlong (christoffelBilinear (g.pullbackCoefficients cb.symm))
      (cb ∘ u) (fun q => mfderiv (𝓡 n) (𝓡 n) cb (u q) (V q)) d p = _
    rw [covDerivAlong_congr_base _ _ hub, covDerivAlong_congr _ _ hVb, htrans]
    change fderiv ℝ ((extChartAt (𝓡 n) b) ∘ (extChartAt (𝓡 n) a).symm)
      (extChartAt (𝓡 n) a (u p)) _ = _
    exact hvalue
  rw [heq, (isInvertible_mfderiv_extChartAt ha).self_apply_inverse]

end Manifold

end PoincareConjecture.ConnectionVariation

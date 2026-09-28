import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.ChartVectorField
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_chart_curve (p : M) (γ : ℝ → M) (s : ℝ)
    (hq : γ s ∈ (chartAt E p).source)
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s) :
    HasDerivAt (fun t ↦ (chartAt E p) (γ t))
      (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) (γ s) (curveVelocity γ s)) s := by
  have he := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hq
  convert! (he.hasMFDerivAt.comp s hγ.hasMFDerivAt).hasFDerivAt.hasDerivAt using 1

set_option backward.isDefEq.respectTransparency false in
theorem chartVectorField_param_smooth (p : M) (v : ℝ → E) (U : Set ℝ)
    (hv : ContDiffOn ℝ ∞ v U) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ Bundle.TotalSpace.mk' E z.2 (chartVectorField p (v z.1) z.2))
      (U ×ˢ (chartAt E p).source) := by
  have hp : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ ((chartAt E p) z.2, v z.1))
      (U ×ˢ (chartAt E p).source) :=
    (contMDiffOn_chart.comp contMDiff_snd.contMDiffOn (fun z hz ↦ hz.2)).prodMk
      (hv.contMDiffOn.comp contMDiff_fst.contMDiffOn (fun z hz ↦ hz.1))
  have htv : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun z : ℝ × M ↦ (⟨(chartAt E p) z.2, v z.1⟩ : TangentBundle (𝓡 n) E))
      (U ×ˢ (chartAt E p).source) := by
    have hmodel : ContMDiff ((𝓡 n).prod (𝓡 n)) ((𝓡 n).prod (𝓡 n)) ∞
        (fun q : E × E ↦ (⟨q.1, q.2⟩ : TangentBundle (𝓡 n) E)) := by
      convert! (contMDiff_tangentBundleModelSpaceHomeomorph_symm (I := 𝓡 n) (n := ∞)) using 1
      rw [chartedSpaceSelf_prod]
      rfl
    exact hmodel.comp_contMDiffOn hp
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt E p).symm (chartAt E p).target :=
    contMDiffOn_chart_symm
  have ht := hc.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt E p).open_target.uniqueMDiffOn
  have h := ht.comp htv (fun z hz ↦ (chartAt E p).map_source hz.2)
  apply h.congr
  intro z hz
  change Bundle.TotalSpace.mk' E z.2 (chartVectorField p (v z.1) z.2) =
    Bundle.TotalSpace.mk' E ((chartAt E p).symm ((chartAt E p) z.2))
      (mfderivWithin (𝓡 n) (𝓡 n) (chartAt E p).symm (chartAt E p).target
        ((chartAt E p) z.2) (v z.1))
  rw [mfderivWithin_of_isOpen (chartAt E p).open_target ((chartAt E p).map_source hz.2)]
  have heq := chartVectorField_at_inverse p (v z.1) ((chartAt E p) z.2)
    ((chartAt E p).map_source hz.2)
  rw [(chartAt E p).left_inv hz.2] at heq ⊢
  exact congrArg (Bundle.TotalSpace.mk' E z.2) heq

set_option backward.isDefEq.respectTransparency false in
theorem curveVelocityWithin_inverseChart (p : M) (a : ℝ → E) (I : Set ℝ)
    (s : ℝ) (v : E) (hI : UniqueDiffWithinAt ℝ I s) (ha : HasDerivAt a v s)
    (hy : a s ∈ (chartAt E p).target) :
    curveVelocityWithin (n := n) (fun r ↦ (chartAt E p).symm (a r)) I s =
      mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (a s) v := by
  have hc := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt_symm hy
  have haM := ha.differentiableAt.mdifferentiableAt
  have hwithin := mfderivWithin_eq_mfderiv hI.uniqueMDiffWithinAt (hc.comp s haM)
  have hcomp := mfderiv_comp s hc haM
  have h := congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓡 n) ((chartAt E p).symm (a s)) ↦ L 1)
    (hwithin.trans hcomp)
  have hA : fderiv ℝ a s 1 = v := by
    exact (congrArg (fun L : ℝ →L[ℝ] E ↦ L 1) ha.hasFDerivAt.fderiv).trans
      (ContinuousLinearMap.toSpanSingleton_apply_one ℝ v)
  have hAm : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) a s 1 = v := by
    exact (congrArg (fun L : ℝ →L[ℝ] E ↦ L 1)
      (mfderiv_eq_fderiv (f := a) (x := s))).trans hA
  exact h.trans (congrArg (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (a s)) hAm)

noncomputable def chartCurveVelocityExtension (p : M) (a v : ℝ → E)
    (U I : Set ℝ) (hU : IsOpen U) (hIU : I ⊆ U) (hI : UniqueDiffOn ℝ I)
    (hv : ContDiffOn ℝ ∞ v U) (ha : ∀ s ∈ I, HasDerivAt a (v s) s)
    (hy : ∀ s ∈ I, a s ∈ (chartAt E p).target) :
    ParametricAlongCurveExtensionOn (n := n) I (fun r ↦ (chartAt E p).symm (a r))
      (curveVelocityWithin (n := n) (fun r ↦ (chartAt E p).symm (a r)) I) where
  extension := fun s ↦ chartVectorField p (v s)
  domain := U ×ˢ (chartAt E p).source
  open_domain := hU.prod (chartAt E p).open_source
  graph_mem := fun s hs ↦ ⟨hIU hs, (chartAt E p).map_target (hy s hs)⟩
  smooth := chartVectorField_param_smooth p v U hv
  agrees := by
    intro s hs
    rw [curveVelocityWithin_inverseChart p a I s (v s) (hI s hs) (ha s hs) (hy s hs)]
    exact chartVectorField_at_inverse p (v s) (a s) (hy s hs)

set_option backward.isDefEq.respectTransparency false in
theorem chartCurveVelocityExtension_pullback {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (p : M) (a v : ℝ → E)
    (U I : Set ℝ) (hU : IsOpen U) (hIU : I ⊆ U) (hI : UniqueDiffOn ℝ I)
    (hv : ContDiffOn ℝ ∞ v U) (ha : ∀ s ∈ I, HasDerivAt a (v s) s)
    (hy : ∀ s ∈ I, a s ∈ (chartAt E p).target)
    (s : ℝ) (hs : s ∈ I) (w : E) (hdv : HasDerivAt v w s) :
    pullbackCovariantDerivative F time (fun r ↦ (chartAt E p).symm (a r))
      (curveVelocityWithin (n := n) (fun r ↦ (chartAt E p).symm (a r)) I) I
      (chartCurveVelocityExtension p a v U I hU hIU hI hv ha hy) s =
        mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (a s) w +
          (F.connection (time s)).connection (chartVectorField p (v s))
            ((chartAt E p).symm (a s))
            (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm (a s) (v s)) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (time s)).toRiemannianMetric⟩
  have hparam : HasDerivAt
      (fun r ↦ chartVectorField p (v r) ((chartAt E p).symm (a s)))
      (chartVectorField p w ((chartAt E p).symm (a s))) s := by
    let L : E →L[ℝ] TangentSpace (𝓡 n) ((chartAt E p).symm (a s)) :=
      (mfderiv (𝓡 n) (𝓡 n) (chartAt E p) ((chartAt E p).symm (a s))).inverse
    change HasDerivAt (fun r ↦ L (v r)) (L w) s
    simpa only [zero_apply, zero_add] using (hasDerivAt_const s L).clm_apply hdv
  change deriv (fun r ↦ chartVectorField p (v r) ((chartAt E p).symm (a s))) s +
    (F.connection (time s)).connection (chartVectorField p (v s)) ((chartAt E p).symm (a s))
      (curveVelocityWithin (n := n) (fun r ↦ (chartAt E p).symm (a r)) I s) = _
  exact congrArg₂ (· + ·)
    (hparam.deriv.trans (chartVectorField_at_inverse p w (a s) (hy s hs)))
    (congrArg ((F.connection (time s)).connection (chartVectorField p (v s))
      ((chartAt E p).symm (a s)))
      (curveVelocityWithin_inverseChart p a I s (v s) (hI s hs) (ha s hs) (hy s hs)))

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

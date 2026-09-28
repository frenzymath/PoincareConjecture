import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.AlongCurve.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Inverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem geodesic_equation_of_comp
    {B C : E → E →L[ℝ] E →L[ℝ] ℝ} {f : E → E} {u : ℝ → E} {t : ℝ}
    (hB : DifferentiableAt ℝ B (u t)) (hC : DifferentiableAt ℝ C (f (u t)))
    (hBinv : (B (u t)).IsInvertible) (hCinv : (C (f (u t))).IsInvertible)
    (hCsymm : ∀ a b, C (f (u t)) a b = C (f (u t)) b a)
    (hf : ContDiffAt ℝ ∞ f (u t)) (hi : Function.Bijective (fderiv ℝ f (u t)))
    (hmetric : ∀ᶠ y in 𝓝 (u t), ∀ a b,
      B y a b = C (f y) (fderiv ℝ f y a) (fderiv ℝ f y b))
    (hu : ContDiffAt ℝ ∞ u t)
    (hgeo : deriv (deriv (f ∘ u)) t =
      -coordinateChristoffel C (f (u t)) (deriv (f ∘ u) t) (deriv (f ∘ u) t)) :
    deriv (deriv u) t = -coordinateChristoffel B (u t) (deriv u t) (deriv u t) := by
  have hfirst : deriv (f ∘ u) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ f (u s) (deriv u s)) := by
    have hfn := ((hf.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp))
    have hun := ((hu.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp))
    filter_upwards [hu.continuousAt.eventually hfn, hun] with s hfs hus
    exact (hfs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      (hus.differentiableAt (by simp)).hasDerivAt |>.deriv
  have hud : DifferentiableAt ℝ (deriv u) t := by
    exact (hu.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hd := (((hf.fderiv_right (m := ∞) (by simp)).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt t
      (hu.differentiableAt (by simp)).hasDerivAt).clm_apply hud.hasDerivAt
  have hsecond := hfirst.deriv_eq.trans hd.deriv
  have htrans := coordinateChristoffel_change_coordinates hB hC hBinv hCinv hCsymm
    hf hi.2 hmetric (deriv u t)
  apply hi.1
  rw [map_neg, htrans]
  rw [hfirst.self_of_nhds, hsecond] at hgeo
  dsimp only [Function.comp_def] at hgeo
  apply eq_neg_of_add_eq_zero_left
  calc
    _ = (fderiv ℝ (fderiv ℝ f) (u t) (deriv u t) (deriv u t) +
        fderiv ℝ f (u t) (deriv (deriv u) t)) +
        coordinateChristoffel C (f (u t)) (fderiv ℝ f (u t) (deriv u t))
          (fderiv ℝ f (u t) (deriv u t)) := by abel
    _ = 0 := by rw [hgeo]; abel

end PoincareConjecture.CoordinateExponential

namespace PoincareConjecture.RiemannianMetric

open ConnectionAlongCurve CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem deriv2_lift_eq_neg_christoffel
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {u : ℝ → EuclideanSpace ℝ (Fin n)}
    {γ : ℝ → M} {I : Set ℝ} {t : ℝ}
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (u t))
    (hi : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e (u t)))
    (hu : ContDiffAt ℝ ∞ u t) (hγ : g.IsGeodesicOn γ I) (ht : t ∈ I)
    (hproj : (fun s => e (u s)) =ᶠ[𝓝 t] γ) :
    deriv (deriv u) t =
      -coordinateChristoffel (g.pullbackCoefficients e) (u t) (deriv u t) (deriv u t) := by
  let p := e (u t)
  let c := extChartAt (𝓡 n) p
  let f := c ∘ e
  let C := g.pullbackCoefficients c.symm
  have hp : e (u t) ∈ c.source := mem_extChartAt_source p
  have hpt : e (u t) = γ t := hproj.self_of_nhds
  have hγp : γ t ∈ c.source := hpt ▸ hp
  have hf : ContDiffAt ℝ ∞ f (u t) := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (by simpa only [c, extChartAt_source] using hp)).comp _ he)
  have hchain := mfderiv_comp (u t)
    (mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source] using hp))
    (he.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  have hfi : Function.Bijective (fderiv ℝ f (u t)) := by
    rw [hchain]
    exact (isInvertible_mfderiv_extChartAt hp).bijective.comp hi
  have hC : ContDiffAt ℝ ∞ C (f (u t)) :=
    (g.contDiffOn_chartCoefficients p).contDiffAt
      ((isOpen_extChartAt_target p).mem_nhds (c.map_source hp))
  have hmetric : ∀ᶠ y in 𝓝 (u t), ∀ a b,
      g.pullbackCoefficients e y a b = C (f y) (fderiv ℝ f y a) (fderiv ℝ f y b) := by
    have hen := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (1 : ℕ∞ω) ≠ ∞)).mp
      (he.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp))
    filter_upwards [hen, he.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source p).mem_nhds hp)] with y hey hyp a b
    change e y ∈ c.source at hyp
    have hc := mfderiv_comp y
      (mdifferentiableAt_extChartAt (by simpa only [c, extChartAt_source] using hyp))
      (hey.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at hc
    have hinner := chartField_inner g (q := fun _ : ℝ => e y)
      (fun _ => mfderiv (𝓡 n) (𝓡 n) e y a)
      (fun _ => mfderiv (𝓡 n) (𝓡 n) e y b) (t := 0) hyp
    dsimp only [chartField] at hinner
    change g.pullbackCoefficients e y a b = _
    rw [hc]
    exact hinner.symm
  apply geodesic_equation_of_comp
    ((g.contDiffAt_pullbackCoefficients he).differentiableAt (by simp))
    (hC.differentiableAt (by simp)) (g.isInvertible_pullbackCoefficients hi.1)
    (g.isInvertible_chartCoefficients p (c.map_source hp)) (fun a b => g.symm _ _ _)
    hf hfi hmetric hu
  have heq : (f ∘ u) =ᶠ[𝓝 t] (c ∘ γ) :=
    hproj.mono fun s hs => congrArg c hs
  have hode := (hγ.hasDerivAt_chart_at ht p hγp).2.deriv
  rw [heq.deriv_eq, heq.deriv.deriv_eq]
  change deriv (deriv (c ∘ γ)) t =
    -coordinateChristoffel C (c (e (u t))) (deriv (c ∘ γ) t) (deriv (c ∘ γ) t)
  rw [hpt]
  exact hode

theorem pullback_velocity_inner_eq_of_lift
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {u : ℝ → EuclideanSpace ℝ (Fin n)}
    {γ : ℝ → M} {t : ℝ}
    (he : MDifferentiableAt (𝓡 n) (𝓡 n) e (u t))
    (hu : DifferentiableAt ℝ u t) (hproj : (e ∘ u) =ᶠ[𝓝 t] γ) :
    g.pullbackCoefficients e (u t) (deriv u t) (deriv u t) =
      g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
  have hd := mfderiv_comp t he hu.mdifferentiableAt
  rw [hproj.mfderiv_eq, mfderiv_eq_fderiv] at hd
  have hv := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1) hd
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1 =
    mfderiv (𝓡 n) (𝓡 n) e (u t) (fderiv ℝ u t 1) at hv
  rw [fderiv_eq_smul_deriv, one_smul] at hv
  change g.inner (e (u t)) (mfderiv (𝓡 n) (𝓡 n) e (u t) (deriv u t))
    (mfderiv (𝓡 n) (𝓡 n) e (u t) (deriv u t)) = _
  rw [← hv, show e (u t) = γ t from hproj.self_of_nhds]

end PoincareConjecture.RiemannianMetric

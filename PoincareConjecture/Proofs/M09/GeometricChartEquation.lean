import PoincareConjecture.Proofs.M09.ChartVelocity
import PoincareConjecture.Proofs.M09.PullbackExtension
import PoincareConjecture.Proofs.M09.SquareChartPairing









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem pullbackCovariantDerivative_chart_velocity {J : Set ℝ} (F : RicciFlow n M J)
    (time : ℝ → ℝ) (p : M) (γ : ℝ → M) (v : ℝ → V)
    (U I : Set ℝ) (hU : IsOpen U) (hIU : I ⊆ U) (hI : UniqueDiffOn ℝ I)
    (hv : ContDiffOn ℝ ∞ v U)
    (hγ : ∀ s ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (ha : ∀ s ∈ I, HasDerivAt (fun t ↦ (chartAt V p) (γ t)) (v s) s)
    (hq : ∀ s ∈ I, γ s ∈ (chartAt V p).source)
    (E : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (s : ℝ) (hs : s ∈ I) (w : V) (hdv : HasDerivAt v w s) :
    pullbackCovariantDerivative F time γ (curveVelocityWithin γ I) I E s =
      chartVectorField p w (γ s) +
        (F.connection (time s)).connection (chartVectorField p (v s)) (γ s)
          (curveVelocityWithin γ I s) := by
  rw [pullbackCovariantDerivative_extension_independent F time γ _ I E
    (chartVelocityExtensionAlong p γ v U I hU hIU hI hv hγ ha hq) s hs
      (hI s hs) (hγ s hs)]
  exact chartVelocityExtensionAlong_pullback F time p γ v U I hU hIU hI
    hv hγ ha hq s hs w hdv

set_option backward.isDefEq.respectTransparency false in
theorem regularizedCoordinatePhase_chart_pairing {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T b : ℝ) (hb : 0 < b)
    (hwindow : Set.Icc (T - b) T ⊆ J) (p : M) (s : ℝ)
    (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (x : M) (hx : x ∈ (chartAt V p).source) (v w : V) :
    let B := (regularizedCoordinatePhase (squareChartMetric F T p)
      (squareChartScalar F T p) (s, ((chartAt V p) x, v))).2
    (F.metric (T - s ^ 2)).inner x
        (chartVectorField p B x + (F.connection (T - s ^ 2)).connection
          (chartVectorField p v) x (chartVectorField p v x)) (chartVectorField p w x) -
      2 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature x
        (chartVectorField p w x) +
      4 * s * (F.connection (T - s ^ 2)).ricci x
        (chartVectorField p v x) (chartVectorField p w x) = 0 := by
  let B := (regularizedCoordinatePhase (squareChartMetric F T p)
    (squareChartScalar F T p) (s, ((chartAt V p) x, v))).2
  have ht := (chartAt V p).map_source hx
  have h := regularizedCoordinatePhase_geometric_pairing F hM04 T b hb hwindow p s hs
    ((chartAt V p) x) v w ht
  rw [← chartVectorField_at_inverse p B _ ht,
    ← chartVectorField_at_inverse p v _ ht,
    ← chartVectorField_at_inverse p w _ ht] at h
  let Q : M → ℝ := fun q ↦
    (F.metric (T - s ^ 2)).inner q
        (chartVectorField p B q + (F.connection (T - s ^ 2)).connection
          (chartVectorField p v) q (chartVectorField p v q)) (chartVectorField p w q) -
      2 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature q
        (chartVectorField p w q) +
      4 * s * (F.connection (T - s ^ 2)).ricci q
        (chartVectorField p v q) (chartVectorField p w q)
  change Q ((chartAt V p).symm ((chartAt V p) x)) = 0 at h
  change Q x = 0
  exact (congrArg Q ((chartAt V p).left_inv hx)).symm.trans h

set_option backward.isDefEq.respectTransparency false in
theorem regularizedEquation_iff_coordinate_acceleration {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (γ : ℝ → M) (v : ℝ → V)
    (U I : Set ℝ) (hU : IsOpen U) (hIU : I ⊆ U) (hI : UniqueDiffOn ℝ I)
    (hv : ContDiffOn ℝ ∞ v U)
    (hγ : ∀ s ∈ I, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ s)
    (ha : ∀ s ∈ I, HasDerivAt (fun t ↦ (chartAt V p) (γ t)) (v s) s)
    (hq : ∀ s ∈ I, γ s ∈ (chartAt V p).source)
    (E : ParametricAlongCurveExtensionOn (n := n) I γ (curveVelocityWithin (n := n) γ I))
    (s : ℝ) (hs : s ∈ I) (htime : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b))
    (w : V) (hdv : HasDerivAt v w s) :
    regularizedLGeodesicEquation F T γ I E s ↔
      w = (regularizedCoordinatePhase (squareChartMetric F T p)
        (squareChartScalar F T p) (s, ((chartAt V p) (γ s), v s))).2 := by
  let B := (regularizedCoordinatePhase (squareChartMetric F T p)
    (squareChartScalar F T p) (s, ((chartAt V p) (γ s), v s))).2
  let g := F.metric (T - s ^ 2)
  let L : V →L[ℝ] TangentSpace (𝓡 n) (γ s) :=
    (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) (γ s)).inverse
  have hvel : curveVelocityWithin γ I s = L (v s) :=
    ((chartVelocityExtensionAlong p γ v U I hU hIU hI hv hγ ha hq).agrees s hs).symm
  have hpull := pullbackCovariantDerivative_chart_velocity F (fun r ↦ T - r ^ 2)
    p γ v U I hU hIU hI hv hγ ha hq E s hs w hdv
  have hp (z : V) := regularizedCoordinatePhase_chart_pairing F hM04 T b hb hwindow
    p s htime (γ s) (hq s hs) (v s) z
  have hlinv : (mfderiv (𝓡 n) (𝓡 n) (chartAt V p) (γ s)).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 n) p).mfderiv (hq s hs), rfl⟩
  constructor
  · intro heq
    have he := heq (L (w - B))
    unfold regularizedEulerResidual at he
    rw [hpull, hvel] at he
    have heB := hp (w - B)
    have hzero : g.inner (γ s) (L (w - B)) (L (w - B)) = 0 := by
      change g.inner (γ s) (L w + _) (L (w - B)) - _ + _ = 0 at he
      change g.inner (γ s) (L B + _) (L (w - B)) - _ + _ = 0 at heB
      rw [map_add, add_apply] at he heB
      have hdifference : g.inner (γ s) (L w) (L (w - B)) -
          g.inner (γ s) (L B) (L (w - B)) = 0 := by
        change g.inner (γ s) (L B) (L (w - B)) +
          g.inner (γ s) ((F.connection (T - s ^ 2)).connection
            (chartVectorField p (v s)) (γ s) (L (v s))) (L (w - B)) -
          2 * s ^ 2 * scalarCurvatureDifferential F (fun r ↦ T - r ^ 2) γ s
            (L (w - B)) +
          4 * s * (F.connection (T - s ^ 2)).ricci (γ s) (L (v s)) (L (w - B)) = 0 at heB
        linarith
      calc
        _ = g.inner (γ s) (L w) (L (w - B)) -
            g.inner (γ s) (L B) (L (w - B)) :=
          congrArg (fun A : TangentSpace (𝓡 n) (γ s) →L[ℝ] ℝ ↦ A (L (w - B)))
            (map_sub ((g.inner (γ s)).comp L) w B)
        _ = 0 := hdifference
    have hLzero : L (w - B) = 0 := by
      by_contra hne
      exact (ne_of_gt (g.pos (γ s) (L (w - B)) hne)) hzero
    have hwb : w - B = 0 := by
      apply hlinv.inverse.injective
      exact hLzero.trans L.map_zero.symm
    exact sub_eq_zero.mp hwb
  · intro heq W
    obtain ⟨z, hz⟩ := hlinv.inverse.surjective W
    change L z = W at hz
    rw [← hz]
    unfold regularizedEulerResidual
    rw [hpull, hvel, heq]
    exact hp z

end PoincareConjecture.Proofs.M09

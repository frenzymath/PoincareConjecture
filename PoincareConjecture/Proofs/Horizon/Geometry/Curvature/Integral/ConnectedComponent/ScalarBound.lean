import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.ConnectedComponent.Equivalence
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Reduction.Connected
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Similarity

open Set MeasureTheory PoincareConjecture
open scoped Manifold ContDiff Bundle
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem PoincareConjecture.RiemannianMetric.component_scalar_bound_of_diffeomorph
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
    (g : PoincareConjecture.RiemannianMetric n M) (h : PoincareConjecture.RiemannianMetric n N)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hm : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = h.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w))
    (K : M → ℝ) (hKc : Continuous K) (hK : ∀ x, 0≤K x)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x),
      -K x ≤ g.leviCivitaData.sectionalCurvature x v w) {C L : ℝ}
    (hbound : ∀ p : N,
      let hC := h.connectedComponentMetric p
      ∀ E : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p → ℝ,
      Continuous E → (∀ x, 0≤E x) →
      (∀ x (v w : TangentSpace (𝓡 n) x),
        -E x ≤ hC.leviCivitaData.sectionalCurvature x v w) →
      (∫ x, max 0 (hC.leviCivitaData.scalarCurvature x) ∂hC.volumeMeasure) ≤
        C*(L+∫ x, E x ∂hC.volumeMeasure)) (p : M) :
    (∫ x, max 0 ((g.connectedComponentMetric p).leviCivitaData.scalarCurvature x)
      ∂(g.connectedComponentMetric p).volumeMeasure) ≤
      C*(L+∫ x, K x ∂(g.connectedComponentMetric p).volumeMeasure) := by
  let E := Poincare.connectedComponentDiffeomorph e p
  let gC := g.connectedComponentMetric p
  let hC := h.connectedComponentMetric (e p)
  let Kc : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p → ℝ :=
    fun x => K x
  have hgeom := g.connectedComponentMetric_geometry_diffeomorph h e hm p
  have hsecs (x : Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin n)) p)
      (v w : TangentSpace (𝓡 n) x) :
      -Kc x ≤ gC.leviCivitaData.sectionalCurvature x v w := by
    rw [RiemannianMetric.sectionalCurvature_connectedComponentMetric g g.leviCivitaData]
    exact hsec x _ _
  have hsect := gC.leviCivitaData.sectionalCurvature_lower_bound_of_metric_similarity
    hC.leviCivitaData E (a := 1) (by norm_num)
    (fun x v w => by simpa only [one_mul] using (hgeom.1 x v w).symm) hsecs
  have hb := hbound (e p) (Kc ∘ E.symm)
    ((hKc.comp continuous_subtype_val).comp E.symm.contMDiff.continuous)
    (fun x => hK (E.symm x))
    (by simpa only [inv_one, one_mul, Function.comp_apply] using hsect)
  rw [hgeom.2.2.2.2.2 (fun z => max 0 z), hgeom.2.2.2.2.1 Kc]
  exact hb

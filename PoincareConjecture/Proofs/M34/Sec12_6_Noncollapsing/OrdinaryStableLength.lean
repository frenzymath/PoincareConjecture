import PoincareConjecture.Proofs.M34.Sec12_6_Noncollapsing.OrdinaryCaptureData
import PoincareConjecture.Proofs.M10.MinimizingLifts










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  {I : SpacetimeInterval} {F : RicciFlow n M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)
  (hRicci : IntrinsicGeneralizedRicciEquation R.leafwiseConnection)
  {T taumax : ℝ} (hT : T ∈ I.domain)
  (out : M14OrdinaryCaptureOutput (ordinaryProductLGeometry R hRicci) M I
    R.product.productCylinder R.product.productMetric F T taumax
    (ordinaryProductCaptureData (I := I) (F := F) R hRicci hT taumax))

include hT out



theorem ordinaryProduct_minimizing_of_eqOn {a b : ℝ}
    {x y x' y' : (ordinaryProductLGeometry R hRicci).Point}
    (p : M14BackwardPath (ordinaryProductLGeometry R hRicci) T a b x y)
    (q : M14BackwardPath (ordinaryProductLGeometry R hRicci) T a b x' y')
    (hb : b ≤ taumax) (hp : M14IsMinimizing p)
    (hpq : EqOn p.curve q.curve (Icc a b)) : M14IsMinimizing q := by
  have hx : x ∈ range R.product.productCylinder.toSpacetime := by
    rw [ordinaryProductCylinder_range]; trivial
  have hx' : x' ∈ range R.product.productCylinder.toSpacetime := by
    rw [ordinaryProductCylinder_range]; trivial
  have hpc : ∀ s ∈ Icc a b, p.curve s ∈ range R.product.productCylinder.toSpacetime := by
    intro s _; rw [ordinaryProductCylinder_range]; trivial
  have hqc : ∀ s ∈ Icc a b, q.curve s ∈ range R.product.productCylinder.toSpacetime := by
    intro s _; rw [ordinaryProductCylinder_range]; trivial
  apply (out.minimizing_transport a b x' y' hb hx' q hqc).mpr
  apply M10.minimizing_of_eqOn ((out.minimizing_transport a b x y hb hx p hpc).mp hp)
  intro s hs
  exact congrArg (ordinaryProductProjection R.product) (hpq hs)



theorem ordinaryProduct_stable_reduced_length {tau : ℝ}
    {x : (ordinaryProductLGeometry R hRicci).Point}
    (E : M14ExponentialFamily (ordinaryProductLGeometry R hRicci) T x)
    (H : M14StableSet (ordinaryProductLGeometry R hRicci) T tau x E)
    (hmax : tau ≤ taumax) (Z : (ordinaryProductLGeometry R hRicci).Horizontal x)
    (hZ : Z ∈ H.carrier) :
    E.reduced_length Z (Real.sqrt tau) = reducedLength F T
      (ordinaryProductProjection R.product x)
      (ordinaryProductProjection R.product (H.endpoint_map Z)) tau := by
  have hs := H.survivor Z hZ
  have hpos := Real.sqrt_pos.mpr H.tau_pos
  have hsq := Real.sq_sqrt H.tau_pos.le
  have hmin : M14IsMinimizing (E.path Z (Real.sqrt tau) hs hpos) := by
    have hex : ∃ p : M14BackwardPath (ordinaryProductLGeometry R hRicci)
        T 0 ((Real.sqrt tau) ^ 2) x (H.endpoint_map Z),
        EqOn p.curve (fun r => E.gamma Z (Real.sqrt r))
          (Icc 0 ((Real.sqrt tau) ^ 2)) ∧ M14IsMinimizing p := by
      rw [hsq]
      obtain ⟨p, hp, hmin, _⟩ := H.minimizing_path Z hZ
      exact ⟨p, hp, hmin⟩
    obtain ⟨p, hp, hmin⟩ := hex
    apply ordinaryProduct_minimizing_of_eqOn R hRicci hT out p
      (E.path Z (Real.sqrt tau) hs hpos) (by rwa [hsq]) hmin
    intro r hr
    exact (hp hr).trans (E.path_coherent Z (Real.sqrt tau) hs hpos r hr).symm
  rw [E.reduced_length_global_eq Z (Real.sqrt tau) hs hpos hmin, hsq,
    ← H.endpoint_map_eq Z hZ]
  apply out.reduced_length_transport tau x (H.endpoint_map Z) H.tau_pos hmax
    E.base_time (H.endpoint_time Z hZ)
  all_goals rw [ordinaryProductCylinder_range]; trivial

end PoincareConjecture.M34

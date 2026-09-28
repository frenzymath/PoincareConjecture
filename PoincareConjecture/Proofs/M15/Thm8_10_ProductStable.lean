import PoincareConjecture.Proofs.M15.Thm8_10_OrdinaryCapture
import PoincareConjecture.Proofs.M15.Thm8_10_StableSurvival
import PoincareConjecture.Proofs.M08.PathCongruence











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {I : SpacetimeInterval}




theorem ordinaryProduct_exists_stableSet
    (F : RicciFlow n M I.domain)
    (P : OrdinaryProductRicciGeometry F.metric I)
    (H : GeneralizedLGeometryConclusion (ordinaryProductTransport F P))
    {T tau taumax : ℝ}
    (capture : M14OrdinaryCaptureData (ordinaryProductTransport F P) M I
      P.product.productCylinder (ordinaryProductCylinderMetric F P) F T taumax)
    (out : M14OrdinaryCaptureOutput (ordinaryProductTransport F P) M I
      P.product.productCylinder (ordinaryProductCylinderMetric F P) F T taumax capture)
    (htau : 0 < tau) (htau_le : tau ≤ taumax)
    (x : (ordinaryProductTransport F P).Point)
    (hbase : (ordinaryProductTransport F P).spacetime.timeFunction x = T)
    (E : M14ExponentialFamily (ordinaryProductTransport F P) T x) :
    Nonempty (M14StableSet (ordinaryProductTransport F P) T tau x E) := by
  let G := ordinaryProductTransport F P
  let e := P.product.productCylinder
  obtain ⟨q, hq0, _, hqmin, _⟩ := out.L.reduced_length_attained tau htau htau_le x.2 x.2
  obtain ⟨p, hpcurve⟩ := capture.path_lift 0 tau q
  let z : G.Point := e.toSpacetime (⟨T - 0, q.time_mem 0 ⟨le_rfl, q.ordered.le⟩⟩, q.curve 0)
  let y : G.Point := e.toSpacetime
    (⟨T - tau, q.time_mem tau ⟨q.ordered.le, le_rfl⟩⟩, q.curve tau)
  have hcap : ∀ s ∈ Icc 0 tau, p.curve s ∈ range e.toSpacetime := by
    intro s _
    rw [ordinaryProductCylinder_range F P]
    exact mem_univ _
  let r := capture.path_map 0 tau z y p hcap
  have htrace : EqOn r.curve q.curve (Icc 0 tau) := by
    intro s hs
    have hc := (capture.path_capture_eq 0 tau z y p hcap s hs).trans (hpcurve s hs).symm
    exact congrArg Prod.snd (e.embedding.injective hc)
  have hrmin : IsMinimizingBackwardLPath F T 0 tau r := by
    intro k hk0 hktau
    rw [M08.backwardLLength_congr F T htau.le htrace]
    exact hqmin k (hk0.trans (htrace ⟨le_rfl, htau.le⟩))
      (hktau.trans (htrace ⟨htau.le, le_rfl⟩))
  have hzcap : z ∈ range e.toSpacetime := by
    rw [ordinaryProductCylinder_range F P]
    exact mem_univ _
  have hpmin : M14IsMinimizing p :=
    (out.minimizing_transport 0 tau z y htau_le hzcap p hcap).mpr hrmin
  have hz : z = x := by
    change e.toSpacetime _ = x
    rw [P.product.productCylinder_eq]
    apply Prod.ext
    · apply Subtype.ext
      change T - 0 = x.1.val
      change x.1.val = T at hbase
      simpa only [sub_zero] using hbase.symm
    · exact hq0
  have htransport : ∀ (z' : G.Point) (_hz : z' = x)
      (p' : M14BackwardPath G T 0 tau z' y), M14IsMinimizing p' →
      Nonempty (M14StableSet G T tau x E) := by
    intro z' hz' p' hp'
    subst z'
    exact exists_stableSet_of_minimizing H E p' hp'
  exact htransport z hz p hpmin

end PoincareConjecture.Proofs.M15

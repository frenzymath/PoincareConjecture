import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Product.OrdinaryCapture
import PoincareLib.Geometry.RicciFlow.Generalized.Noncollapse.Compact.Product.StableSurvival
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.PathCongruence

/-! Adapted from Mapher `PoincareMT/Proofs/M15/Thm8_10_ProductStable.lean` at
`0c5d5c4e1ecbc12703b1994e226df1b15d2e8d39`. See the source mapping in
`references/ricci-flow/mapher/noncollapse/import.json`. -/

/-!
# Actual stable-set existence in the ordinary product

Morgan-Tian Lemma 6.8, p. 108, Definition 6.25, p. 116, and
Proposition 6.28, p. 117, as used in Theorem 8.10, p. 177.
An attained ordinary minimum lifts to a generalized minimum and
therefore supplies the required exponential survivor.
See `references/ricci-flow/mapher/noncollapse/derivations/2026-09-21-product-stable-paths.md`.
-/

set_option autoImplicit false
-- Captured paths use the same interval representatives and tangent instances.
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.Generalized.Noncollapse

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {I : SpacetimeInterval}

/-- Actual capture of an ordinary minimizer supplies a stable-set record
at every positive admissible time. Source: Lemma 6.8, p. 108, and
Definition 6.25, p. 116, used in Theorem 8.10, p. 177. -/
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
    rw [backwardLLength_eq_of_eqOn (F := F) (T := T) htau.le htrace]
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

end PoincareMT.Generalized.Noncollapse

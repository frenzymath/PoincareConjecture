import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Lifetime.Basic.OrdinaryCylinder
import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data

/-!
# Maximal ordinary backward worldlines in Chapter 11

The maximal normalized interval is the full affine-clock preimage of
the original lifetime. A competing cylinder cannot include any other
time, since its value would inhabit an excluded time slice.
Source: Morgan-Tian Theorems 11.1 and 12.28, pp. 269-271, 323-324;
ordinary Chapter 11 derivation, section 6.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}

/-- The actual maximal ordinary worldline at a positive normalization
scale, including every requested physically existing time (Theorem 12.28). -/
noncomputable def ordinaryChapter11MaximalLine
    (R : OrdinaryProductRicciGeometry F.metric I)
    (p : (ordinaryChapter11Flow R).point) (scale duration : ℝ) (hscale : 0 < scale)
    (hrequested : ∀ s ∈ Icc (-duration) 0, p.1 + s / scale ∈ I.domain) :
    GeneralizedMaximalBackwardFlowLine (ordinaryChapter11Flow R) p scale duration := by
  let K : Set ℝ := {s | p.1 + s / scale ∈ I.domain}
  have hzero : 0 ∈ K := by
    simpa only [K, mem_ofPred_eq, zero_div, add_zero] using ordinaryChapter11Point_time_mem R p
  refine {
    maximal_interval := K
    maximal_interval_mem_zero := hzero
    maximal_interval_ordConnected := ?_
    embedding := ordinaryChapter11Cylinder R p scale hscale K {p.2} (fun _ hs => hs)
    zero_identity := ordinaryChapter11Cylinder_zero_identity R p scale hscale K {p.2}
      (fun _ hs => hs) hzero p.2
    requested_interval_subset := hrequested
    maximal := ?_
  }
  · exact I.ordConnected.preimage_mono
      (fun _ _ hab => add_le_add le_rfl (div_le_div_of_nonneg_right hab hscale.le))
  · intro K' e' _ hsub _
    apply Subset.antisymm _ hsub
    intro s hs
    exact ordinaryChapter11Point_time_mem R (e'.pointMap s hs p.2)

end PoincareMT.M34

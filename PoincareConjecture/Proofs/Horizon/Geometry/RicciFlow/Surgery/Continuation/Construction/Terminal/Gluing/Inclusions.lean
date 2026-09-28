import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

def retainedInclusion : U → (cutCarrier I R U hU hd hc).carrier :=
  (cutSystem I R U hU hd).include none

def capInclusion (i : ι) : (R i).output.carrier → (cutCarrier I R U hU hd hc).carrier :=
  (cutSystem I R U hU hd).include (some i)

theorem retainedInclusion_openEmbedding : Topology.IsOpenEmbedding
    (retainedInclusion I R U hU hd hc) := (cutSystem I R U hU hd).include_isOpenEmbedding none

theorem capInclusion_openEmbedding (i : ι) : Topology.IsOpenEmbedding
    (capInclusion I R U hU hd hc i) := (cutSystem I R U hU hd).include_isOpenEmbedding (some i)

theorem retainedInclusion_localDiffeomorph : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (retainedInclusion I R U hU hd hc) :=
  carrier_include_isLocalDiffeomorph (cutSystem I R U hU hd) (cutSystem_smooth I R U hU hd)
    (cutSystem_closed I R U hU hd hc) none

theorem capInclusion_localDiffeomorph (i : ι) : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
    (capInclusion I R U hU hd hc i) :=
  carrier_include_isLocalDiffeomorph (cutSystem I R U hU hd) (cutSystem_smooth I R U hU hd)
    (cutSystem_closed I R U hU hd hc) (some i)

theorem retainedInclusion_metric (x : U) (a b : TangentSpace (𝓡 3) x) :
    (cutMetric I R U hU hd hc).inner (retainedInclusion I R U hU hd hc x)
      (mfderiv (𝓡 3) (𝓡 3) (retainedInclusion I R U hU hd hc) x a)
      (mfderiv (𝓡 3) (𝓡 3) (retainedInclusion I R U hU hd hc) x b) =
        (S.openSubsetMetric U g).inner x a b :=
  (metric_preserves (cutSystem I R U hU hd) (cutSystem_smooth I R U hU hd)
    (cutSystem_closed I R U hU hd hc) (cutPieceMetric I R U)
    (cutSystem_metric I R U hU hd) none x a b).symm

theorem capInclusion_metric (i : ι) (x : (R i).output.carrier)
    (a b : TangentSpace (𝓡 3) x) :
    (cutMetric I R U hU hd hc).inner (capInclusion I R U hU hd hc i x)
      (mfderiv (𝓡 3) (𝓡 3) (capInclusion I R U hU hd hc i) x a)
      (mfderiv (𝓡 3) (𝓡 3) (capInclusion I R U hU hd hc i) x b) =
        (R i).metric.inner x a b :=
  (metric_preserves (cutSystem I R U hU hd) (cutSystem_smooth I R U hU hd)
    (cutSystem_closed I R U hU hd hc) (cutPieceMetric I R U)
    (cutSystem_metric I R U hU hd) (some i) x a b).symm

theorem retainedInclusion_eq_cap (i : ι) (x : U) (hx : x.val ∈ (I i).negativeHalf) :
    retainedInclusion I R U hU hd hc x =
      capInclusion I R U hU hd hc i ((R i).collapse x.val) := by
  apply ((cutSystem I R U hU hd).include_eq_iff none (some i) x _).mpr
  refine ⟨?_, rfl⟩
  change x ∈ ((R i).collarOverlap U hU).source
  rwa [(R i).collarOverlap_source]

theorem retainedInclusion_mem_cap_iff (i : ι) (x : U) :
    retainedInclusion I R U hU hd hc x ∈ range (capInclusion I R U hU hd hc i) ↔
      x.val ∈ (I i).negativeHalf := by
  exact ((cutSystem I R U hU hd).include_mem_range_iff none (some i) x).trans
    (Set.ext_iff.mp ((R i).collarOverlap_source U hU) x)

theorem capInclusion_disjoint : Pairwise (fun i j =>
    Disjoint (range (capInclusion I R U hU hd hc i))
      (range (capInclusion I R U hU hd hc j))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro q ⟨x, rfl⟩ ⟨y, hy⟩
  have hxy := ((cutSystem I R U hU hd).include_eq_iff (some i) (some j) x y).mp hy.symm
  have hx := hxy.1
  change x ∈ (capTransition (fun i => (R i).collarOverlap U hU) i j).source at hx
  rw [capTransition_source_empty _ (collarOverlaps_disjoint I R U hU hd) hij] at hx
  exact hx

theorem cutCarrier_cover (q : (cutCarrier I R U hU hd hc).carrier) :
    q ∈ range (retainedInclusion I R U hU hd hc) ∨
      ∃ i, q ∈ range (capInclusion I R U hU hd hc i) := by
  induction q using Quotient.inductionOn with
  | h a =>
    rcases a with ⟨_ | i, x⟩
    · exact Or.inl ⟨x, rfl⟩
    · exact Or.inr ⟨i, x, rfl⟩

theorem cutCarrier_nonempty : Nonempty (cutCarrier I R U hU hd hc).carrier :=
  hU.map (retainedInclusion I R U hU hd hc)

end PoincareConjecture.Surgery.Terminal.Gluing

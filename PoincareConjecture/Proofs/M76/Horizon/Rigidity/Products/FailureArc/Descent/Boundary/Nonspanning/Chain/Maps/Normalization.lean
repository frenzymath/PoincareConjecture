import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Maps.Construction



set_option autoImplicit false
open Set Geometry Topology TriangleDiskModel PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "Ann" => squareAnnulus 8 1
local notation "Index" => (NonspanningRetainedPiece ⊕ Bool)

structure NonspanningChainAnnulus {SA SM SC D : Set P2} {pA pL pR pC : I01 → P2}
    {s : NonspanningChainGeometry SA SM SC pA pL pR pC} (H : NonspanningChainHole s D) where
  chart : Ann ≃ₜ (T \ interior H.carrier : Set P2)
  chart_PL : chart.IsFinitePL
  outer : ∀ z : Ann, depth 8 (z : P2) = -1 ↔ (chart z : P2) ∈ frontier T
  inner : ∀ z : Ann, depth 8 (z : P2) = 1 ↔ (chart z : P2) ∈ frontier H.carrier

namespace NonspanningChainHole

variable {SA SM SC D : Set P2} {pA pL pR pC : I01 → P2}
  {s : NonspanningChainGeometry SA SM SC pA pL pR pC}
  (H : NonspanningChainHole s D)

theorem nonempty_normalization : Nonempty (NonspanningChainAnnulus H) := by
  obtain ⟨_, _, _, _, _, _, _, _, hT⟩ := exists_disk_attachment_model
  have hT' : IsFinitePLBallPair P2 T (frontier T) :=
    (hT.frontier_eq_of_finrank_eq rfl).symm ▸ hT
  obtain ⟨q, hq, hout, hin⟩ := exists_square_annulus_nested_disks H.ball hT' H.inside
    (show (0 : ℝ) < 1 by norm_num) (show (2 : ℝ) * 1 < 8 by norm_num)
  exact ⟨⟨q, hq, hout, hin⟩⟩

end NonspanningChainHole

namespace NonspanningChainAnnulus

variable {SA SM SC D : Set P2} {pA pL pR pC : I01 → P2}
  {s : NonspanningChainGeometry SA SM SC pA pL pR pC}
  {H : NonspanningChainHole s D} (N : NonspanningChainAnnulus H)

def copy (i : Index) (x : H.sourceSet i) : Ann :=
  N.chart.symm ⟨H.pieceCopy i x, H.pieceCopy_outside i x⟩

theorem chart_copy (i : Index) (x : H.sourceSet i) :
    (N.chart (N.copy i x) : P2) = H.pieceCopy i x :=
  congrArg Subtype.val (N.chart.apply_symm_apply _)

theorem copy_embedding (i : Index) : IsEmbedding (N.copy i) :=
  N.chart.symm.isEmbedding.comp
    ((IsEmbedding.subtypeVal.comp (H.pieceCopy_embedding i)).codRestrict
      (T \ interior H.carrier) (H.pieceCopy_outside i))

theorem copy_representative
    (hS : ∀ i, IsFinitePLBallPair P2 (s.retainedSet i) (frontier (s.retainedSet i)))
    (hD : IsFinitePLBallPair P2 D (frontier D)) (i : Index) :
    ∃ c : P2 → P2, FinitePiecewiseAffineOn c (H.sourceSet i) ∧
      ∀ x : H.sourceSet i, (N.copy i x : P2) = c x := by
  obtain ⟨c, hc, hcv⟩ := H.pieceCopy_representative hS hD i
  obtain ⟨r, hr, hrv⟩ := N.chart_PL.symm
  have hm : MapsTo c (H.sourceSet i) (T \ interior H.carrier) := by
    intro x hx
    rw [← hcv ⟨x, hx⟩]
    exact H.pieceCopy_outside i ⟨x, hx⟩
  refine ⟨r ∘ c, hr.comp hc hm, ?_⟩
  intro x
  change (N.chart.symm ⟨H.pieceCopy i x, H.pieceCopy_outside i x⟩ : P2) = r (c x)
  rw [hrv, hcv]

theorem copy_eq_iff (i j : Index) (x : H.sourceSet i) (y : H.sourceSet j) :
    N.copy i x = N.copy j y ↔ H.pieceCopy i x = H.pieceCopy j y := by
  constructor
  · intro h
    exact Subtype.ext ((N.chart_copy i x).symm.trans
      ((congrArg (fun z : Ann => (N.chart z : P2)) h).trans (N.chart_copy j y)))
  · intro h
    exact congrArg N.chart.symm (Subtype.ext (congrArg (fun z : T => (z : P2)) h))

theorem copy_cover : (⋃ i, range (N.copy i)) = univ := by
  apply eq_univ_of_forall
  intro z
  obtain ⟨i, x, hx⟩ := mem_iUnion.mp (H.pieceCopy_cover.symm.subset (N.chart z).property)
  exact mem_iUnion.mpr ⟨i, x, N.chart.injective (Subtype.ext ((N.chart_copy i x).trans hx))⟩

theorem retained_inner (hD : IsFinitePLBallPair P2 D (frontier D))
    (i : NonspanningRetainedPiece) (x : H.sourceSet (.inl i)) :
    depth 8 (N.copy (.inl i) x : P2) = 1 ↔ (x : P2) ∈ frontier D := by
  rw [N.inner, N.chart_copy, H.ball.isCompact.isClosed.frontier_eq,
    hD.isCompact.isClosed.frontier_eq]
  exact and_congr (H.retained_mem i ⟨x, x.property.1⟩)
    (not_congr (H.retained_interior i ⟨x, x.property.1⟩))

theorem strip_not_inner (b : Bool) (x : H.sourceSet (.inr b)) :
    depth 8 (N.copy (.inr b) x : P2) ≠ 1 := by
  intro hx
  have hfront := (N.inner _).mp hx
  rw [N.chart_copy] at hfront
  exact H.strip_avoid b x (H.ball.1 hfront)

theorem exists_original_map
    {F X ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X]
    (e : ι → OpenPartialHomeomorph X F) {u : P2 → X}
    (hu : PolyhedralPLInCharts e u (T \ interior H.carrier)) :
    ∃ g : P2 → X, PolyhedralPLInCharts e g Ann ∧
      (∀ z : Ann, g z = u (N.chart z)) ∧
      (∀ i (x : H.sourceSet i), g (N.copy i x) = u (H.pieceCopy i x)) ∧
      g '' Ann = u '' (T \ interior H.carrier) := by
  obtain ⟨k, hk, hkv⟩ := N.chart_PL
  let g := u ∘ k
  have hgv (z : Ann) : g z = u (N.chart z) := congrArg u (hkv z).symm
  have hcopy := hk
  obtain ⟨K, hK, hKs, _⟩ := hcopy
  have hm : MapsTo k K.space (T \ interior H.carrier) := by
    intro z hz
    rw [← hkv ⟨z, hKs.subset hz⟩]
    exact (N.chart ⟨z, hKs.subset hz⟩).property
  have hg : PolyhedralPLInCharts e g Ann := hKs ▸
    hu.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hk) hm
  refine ⟨g, hg, hgv, ?_, ?_⟩
  · intro i x
    rw [hgv, N.chart_copy]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨N.chart ⟨z, hz⟩, (N.chart ⟨z, hz⟩).property, (hgv ⟨z, hz⟩).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨N.chart.symm ⟨z, hz⟩, (N.chart.symm ⟨z, hz⟩).property, ?_⟩
      rw [hgv, N.chart.apply_symm_apply]

end NonspanningChainAnnulus
end PoincareConjecture.M76.Dehn

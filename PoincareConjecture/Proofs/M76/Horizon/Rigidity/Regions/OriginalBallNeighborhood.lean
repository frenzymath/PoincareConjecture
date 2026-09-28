import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalBallBoundarySphere
import PoincareConjecture.Proofs.M76.Rigidity.OriginalBoundaryProduct
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallBicollarEnlargement











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.ChartwisePLBall

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {D S U : Set X}

theorem exists_strict_ball_neighborhood (b : ChartwisePLBall e D S)
    (he : PLDomain e D) (hout : Dᶜ.Nonempty) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ D' S' : Set X, Nonempty (ChartwisePLBall e D' S') ∧
      D ⊆ interior D' ∧ D' ⊆ U := by
  have hminus : IsCompact (interior D)ᶜ := isOpen_interior.isClosed_compl.isCompact
  have hnminus : (interior (interior D)ᶜ).Nonempty := by
    obtain ⟨x, hx⟩ := hout
    exact ⟨x, (interior_mono (compl_subset_compl.mpr interior_subset))
      (he.closed.isOpen_compl.interior_eq.symm.subset hx)⟩
  obtain ⟨s, L, HB, c, hL, hc, hi, hbase, _, delta, hdelta, hdeltahalf, hcU, hopen⟩ :=
    he.exists_small_boundary_product_of_interiors_nonempty b.isCompact hminus
      b.isConnected_interior.nonempty hnminus hU (he.closed.frontier_subset.trans hDU)
  obtain ⟨sph⟩ := b.nonempty_boundarySphere
  let HB' := HB.trans (Homeomorph.setCongr b.frontier_eq)
  have hbase' (z : L.space) : c ((z : s → ℝ × (Fin 3 → ℝ)), 0) = HB' z := hbase z
  have hsub : L.space ×ˢ Icc (-delta) delta ⊆ L.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩
  obtain ⟨K, hK, hKs⟩ := L.exists_finite_interval_product hL (by linarith : -delta < delta)
  have hcsmall : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-delta) delta) :=
    hKs ▸ hc.restrict_finite K hK (hKs.subset.trans hsub)
  have hismall : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-delta) delta : Set ((s → ℝ × (Fin 3 → ℝ)) × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.subtypeVal.codRestrict _ (fun z => hsub z.property))
  obtain ⟨a, _, _, D', hb, hDD', hD'sub⟩ := b.exists_bicollar_enlargement sph
    he.cover he.compatible L hL HB' c hdelta hcsmall hismall hbase' (hopen delta hdelta le_rfl)
  exact ⟨D', c '' (L.space ×ˢ {a}), hb, hDD',
    hD'sub.trans (union_subset hDU (image_subset_iff.mpr hcU))⟩

end PoincareConjecture.M76.ChartwisePLBall

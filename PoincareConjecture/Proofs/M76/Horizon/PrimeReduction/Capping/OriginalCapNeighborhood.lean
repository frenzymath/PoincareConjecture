import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.OriginalSphereBicollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Spheres.OriginalBallBoundarySphere
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Collars.OriginalBallBicollarEnlargement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalBallInteriorChart








set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem ChartwisePLBall.exists_enclosing_chart_in_domain
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {D S R U : Set X}
    (b : ChartwisePLBall e D S) (hR : IsCompact R) (he : PLDomain e R)
    (hDR : D ⊆ interior R) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ Q : OpenPartialHomeomorph X V3,
      D ⊆ Q.source ∧ Q.source ⊆ U ∩ interior R ∧ Q.target = ball (0 : V3) 1 ∧
      ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3 := by
  obtain ⟨sph⟩ := b.nonempty_boundarySphere
  let V := U ∩ interior R
  have hV : IsOpen V := hU.inter isOpen_interior
  have hDV : D ⊆ V := subset_inter hDU hDR
  obtain ⟨t,L,HB,c,hL,hc,hi,_,hbase,_,δ,hδ,hδhalf,hcV,hopen⟩ :=
    sph.exists_original_small_bicollar hR he (b.boundary_subset.trans hDR)
      hV (b.boundary_subset.trans hDV)
  have hsub : L.space ×ˢ Icc (-δ) δ ⊆ L.space ×ˢ Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨hz.1,by linarith [hz.2.1],by linarith [hz.2.2]⟩
  obtain ⟨K,hK,hKs⟩ := L.exists_finite_interval_product hL (by linarith : -δ < δ)
  have hcsmall : PolyhedralPLInCharts e c (L.space ×ˢ Icc (-δ) δ) :=
    hKs ▸ hc.restrict_finite K hK (hKs.subset.trans hsub)
  have hismall : Topology.IsEmbedding
      (fun z : (L.space ×ˢ Icc (-δ) δ : Set ((t → ℝ × V3) × ℝ)) => c z) :=
    hi.comp (Topology.IsEmbedding.subtypeVal.codRestrict _ (fun z => hsub z.property))
  obtain ⟨a,_,_,D',⟨b'⟩,hDD',hD'sub⟩ := b.exists_bicollar_enlargement sph
    he.cover he.compatible L hL HB c hδ hcsmall hismall hbase (hopen δ hδ le_rfl)
  obtain ⟨Q,hQS,hQT,_,_,hQ⟩ := b'.exists_original_interior_chart he.compatible
  refine ⟨Q,hQS.symm ▸ hDD',?_,hQT,hQ⟩
  rw [hQS]
  exact interior_subset.trans (hD'sub.trans
    (union_subset hDV (image_subset_iff.mpr (fun _ hz => (hcV hz).1))))

end PoincareConjecture.M76

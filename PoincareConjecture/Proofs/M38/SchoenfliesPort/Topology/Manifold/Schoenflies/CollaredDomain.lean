import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.EmbeddingSupplement
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Neighborhood
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.FromEmbedding
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.HalfSpaceChart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.EuclideanModel
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Models
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.Connected

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false

open Set PoincareConjecture
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem halfspace_chart_of_collar
    (c : OpenPartialHomeomorph RoundCylinderSpace E3)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {K : Set E3} (hK : ∀ y ∈ c.target, y ∈ K ↔ 0 ≤ (c.symm y).2)
    {x : E3} (hx : x ∈ c.target) :
    ∃ e : OpenPartialHomeomorph E3 E3, x ∈ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      e.IsImage K {y | 0 ≤ y 0} := by
  let p := (c.symm x).1
  let e := (c.symm.trans
    ((chartAt E2 p).prod (OpenPartialHomeomorph.refl ℝ))).trans
      (RiemannianMetric.lineModelEquiv 2).toHomeomorph.toOpenPartialHomeomorph
  refine ⟨e, ⟨⟨hx, mem_chart_source E2 p, mem_univ _⟩, mem_univ _⟩, ?_, ?_, ?_⟩
  · apply (RiemannianMetric.lineModelEquiv 2).contDiff.contMDiff.comp_contMDiffOn
    apply ContMDiffOn.prodMk_space
    · apply (contMDiffOn_chart (I := 𝓡 2) (x := p)).comp
      · exact contMDiff_fst.comp_contMDiffOn (hci.mono (fun y hy => hy.1.1))
      · intro y hy
        exact hy.1.2.1
    · exact contMDiff_snd.comp_contMDiffOn (hci.mono (fun y hy => hy.1.1))
  · apply hc.comp
    · apply ContMDiffOn.prodMk
      · apply (contMDiffOn_chart_symm (I := 𝓡 2) (x := p)).comp
        · exact (contDiff_fst.comp
            (RiemannianMetric.lineModelEquiv 2).symm.contDiff).contMDiff.contMDiffOn
        · intro y hy
          exact hy.2.1.1
      · exact (contDiff_snd.comp
          (RiemannianMetric.lineModelEquiv 2).symm.contDiff).contMDiff.contMDiffOn
    · intro y hy
      exact hy.2.2
  · intro y hy
    change 0 ≤ (c.symm y).2 ↔ y ∈ K
    exact (hK y hy.1.1).symm

theorem ball_neighborhood_of_compact_collar_side
    {K : Set E3} (hK : IsCompact K) (hregular : closure (interior K) = K)
    (c : OpenPartialHomeomorph RoundCylinderSpace E3)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    {δ : ℝ} (hδ : 0 < δ) (hsource : univ ×ˢ Ioo (-δ) δ ⊆ c.source)
    (hfront : frontier K = range (fun q : UnitTwoSphere => c (q, 0)))
    (hside : ∀ y ∈ c.target, y ∈ K ↔ 0 ≤ (c.symm y).2) :
    ∃ b : OpenPartialHomeomorph E3 E3,
      Metric.closedBall 0 1 ⊆ b.source ∧ K ⊆ b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      b '' Metric.closedBall 0 1 = K := by
  let : ConnectedSpace UnitTwoSphere := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := E3) (by rw [← Module.finrank_eq_rank]; norm_num)
      0 zero_le_one)
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ c.source :=
    hsource ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩
  have himage : c.symm.IsImage K (univ ×ˢ Ici (0 : ℝ)) := by
    intro y hy
    simpa only [mem_prod, mem_univ, true_and, mem_Ici] using (hside y hy).symm
  have hinterior (y : E3) (hy : y ∈ c.target) :
      y ∈ interior K ↔ 0 < (c.symm y).2 := by
    simpa only [interior_prod_eq, interior_univ, interior_Ici,
      mem_prod, mem_univ, true_and, mem_Ioi] using (himage.interior hy).symm
  have hfronti : frontier (interior K) = frontier K := by
    rw [frontier, hregular, interior_interior, hK.isClosed.frontier_eq]
  let U := c '' (univ ×ˢ Ioo (-δ) δ)
  have hU : IsOpen U := c.isOpen_image_of_subset_source (isOpen_univ.prod isOpen_Ioo) hsource
  have hpos : interior K ∩ U = c '' (univ ×ˢ Ioo 0 δ) := by
    ext y
    constructor
    · rintro ⟨hy, z, hz, rfl⟩
      have ht := (hinterior _ (c.map_source (hsource hz))).mp hy
      rw [c.left_inv (hsource hz)] at ht
      exact ⟨z, ⟨mem_univ _, ht, hz.2.2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hz' : z ∈ univ ×ˢ Ioo (-δ) δ :=
        ⟨mem_univ _, (neg_lt_zero.mpr hδ).trans hz.2.1, hz.2.2⟩
      refine ⟨(hinterior _ (c.map_source (hsource hz'))).mpr ?_, z, hz', rfl⟩
      rw [c.left_inv (hsource hz')]
      exact hz.2.1
  have hconn : IsConnected (interior K) := by
    apply Poincare.Topology.isConnected_of_inter_of_frontier_subset isOpen_interior hU
    · rw [hpos]
      apply ((isConnected_univ : IsConnected (univ : Set UnitTwoSphere)).prod
        (isConnected_Ioo hδ)).image _
      apply c.continuousOn.mono
      intro z hz
      exact hsource ⟨mem_univ _, (neg_lt_zero.mpr hδ).trans hz.2.1, hz.2.2⟩
    · rw [hfronti, hfront]
      rintro _ ⟨q, rfl⟩
      exact ⟨(q, 0), ⟨mem_univ _, neg_lt_zero.mpr hδ, hδ⟩, rfl⟩
    · intro hall
      exact NormedSpace.unbounded_univ ℝ E3 (hall ▸ hK.isBounded.subset interior_subset)
  have hcharts : ∀ x : K, ∃ e : OpenPartialHomeomorph E3 E3,
      x.val ∈ e.source ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧ e.IsImage K {y | 0 ≤ y 0} := by
    intro x
    by_cases hx : x.val ∈ interior K
    · obtain ⟨e, he, hes, hei, himg⟩ :=
        Poincare.Manifold.exists_interior_superlevel_halfspace_chart
          (E := E3) (n := 2) (by simp) (f := fun _ : E3 => (1 : ℝ))
          continuous_const 0 x.val (by norm_num)
      refine ⟨e.restrOpen (interior K) isOpen_interior, ⟨he, hx⟩,
        hes.mono inter_subset_left, hei.mono inter_subset_left, ?_⟩
      intro y hy
      exact iff_of_true ((himg hy.1).mpr (by norm_num)) (interior_subset hy.2)
    · have hxf : x.val ∈ frontier K := ⟨subset_closure x.property, hx⟩
      rw [hfront] at hxf
      obtain ⟨q, hq⟩ := hxf
      exact halfspace_chart_of_collar c hc hci hside (hq ▸ c.map_source (hzero q))
  choose amb hamb using hcharts
  obtain ⟨CS, _, _, _, hman, hemb⟩ :=
    Poincare.Manifold.exists_smooth_embedding_of_halfspace_charts
      (n := 2) (by simp) K amb hamb
  let := CS
  let := hman
  obtain ⟨D⟩ := Poincare.Manifold.nonempty_smoothDomain_interior
    hK (hregular ▸ hconn.closure) hemb
  have hsf := Poincare.isSmoothEmbedding_collar_center c hc hci hzero
  simpa only [hregular] using Poincare.Manifold.SmoothDomain.exists_ball_neighborhood D
    (fun q : UnitTwoSphere => c (q, 0)) hsf (hfronti.trans hfront).symm

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies

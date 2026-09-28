import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Caps.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Compactness.Local
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (I : ι → MetricSurgeryInput K g)
  (R : ∀ i, MetricSurgeryResult g₀ (I i)) (U : Opens S.carrier) (hU : Nonempty U)
  (hd : Pairwise (fun i j => Disjoint ((I i).negativeHalf : Set S.carrier)
    ((I j).negativeHalf : Set S.carrier)))
  (hc : ∀ i, Disjoint (U : Set S.carrier) (I i).neck.central_sphere)

theorem capInclusion_edist_le (i : ι) (x y : (R i).output.carrier) :
    (cutMetric I R U hU hd hc).edist (capInclusion I R U hU hd hc i x)
      (capInclusion I R U hU hd hc i y) ≤ (R i).metric.edist x y := by
  have h := (R i).metric.edist_le_mul_of_inner_mfderiv_le
    (cutMetric I R U hU hd hc)
    ((capInclusion_localDiffeomorph I R U hU hd hc i).contMDiff.of_le (by simp))
    (C := 1) zero_lt_one (fun z v => by
      rw [capInclusion_metric]
      simp) x y
  simpa using h

theorem capInclusion_inner_ball (i : ι) :
    (cutMetric I R U hU hd hc).ball
      (capInclusion I R U hU hd hc i (R i).tip)
      ((I i).neck.scale * (g₀.cylindrical_end.radius + 3)) ⊆
        capInclusion I R U hU hd hc i ''
          ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) := by
  let e := capEmbedding I R U hU hd hc i
  let r₀ := (I i).neck.scale * (g₀.cylindrical_end.radius + 3)
  have hr₀ : 0 < r₀ := mul_pos (I i).neck.scale_pos
    (by linarith [g₀.cylindrical_end.radius_pos])
  have hcompact : IsCompact (closure ((R i).metric.ball (R i).tip r₀)) :=
    (R i).isCompact_closed_cap.of_isClosed_subset isClosed_closure
      (closure_mono (R i).cap_inner_ball)
  have hinv : ∀ y ∈ e.target, ContMDiffAt (𝓡 3) (𝓡 3) 1 e.symm y := by
    intro y hy
    exact ((capEmbedding_symm_smooth I R U hU hd hc i y hy).contMDiffAt
      (e.open_target.mem_nhds hy)).of_le (by simp)
  have hbound : ∀ y ∈ e '' closure ((R i).metric.ball (R i).tip r₀),
      ∀ v : TangentSpace (𝓡 3) y,
      (R i).metric.tangentNorm (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v) ≤
        1 * (cutMetric I R U hU hd hc).tangentNorm y v := by
    rintro y ⟨x, hx, rfl⟩ v
    have hm := capEmbedding_symm_metric I R U hU hd hc i
      (e.map_source (mem_univ x)) v v
    dsimp [RiemannianMetric.tangentNorm]
    rw [hm, one_mul]
  intro y hy
  obtain ⟨r, hdr, hrr₀⟩ := exists_between (ENNReal.toReal_lt_of_lt_ofReal hy)
  have hdist : y ∈ (cutMetric I R U hU hd hc).ball (e (R i).tip) r := by
    change (cutMetric I R U hU hd hc).edist
      (capInclusion I R U hU hd hc i (R i).tip) y < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal (ne_top_of_lt (hy.trans_le le_top))]
    exact (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_nonneg.trans_lt hdr)).mpr hdr
  have hcover := (R i).metric.ball_subset_image_ball_of_inverse_tangentNorm_le
    (cutMetric I R U hU hd hc) e (R i).tip hr₀ (C := 1) zero_lt_one
    (by simpa using hrr₀) hcompact (by simp [e]) hinv hbound hdist
  obtain ⟨x, hx, hxy⟩ := hcover
  refine ⟨x, (R i).cap_inner_ball ?_, hxy⟩
  change (R i).metric.edist (R i).tip x < ENNReal.ofReal (1 * r) at hx
  exact hx.trans_le (ENNReal.ofReal_le_ofReal (by simpa using hrr₀.le))

theorem capInclusion_closed_outer_ball (i : ι) :
    capInclusion I R U hU hd hc i ''
      closure ((R i).cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) ⊆
        {y | (cutMetric I R U hU hd hc).edist
          (capInclusion I R U hU hd hc i (R i).tip) y ≤
            ENNReal.ofReal ((I i).neck.scale * (g₀.cylindrical_end.radius + 5))} := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (R i).output.carrier → Type _) :=
    ⟨(R i).metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : (R i).output.carrier → Type _) :=
    ⟨⟨(R i).metric.inner, (R i).metric.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (R i).output.carrier :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) (R i).output.carrier
  have hclosed : closure ((R i).cap_map ''
      g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4)) ⊆
      {x | (R i).metric.edist (R i).tip x ≤
        ENNReal.ofReal ((I i).neck.scale * (g₀.cylindrical_end.radius + 5))} := by
    apply closure_minimal
    · intro x hx
      have hb : (R i).metric.edist (R i).tip x <
          ENNReal.ofReal ((I i).neck.scale * (g₀.cylindrical_end.radius + 5)) :=
        (R i).cap_outer_ball hx
      exact hb.le
    · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  rintro y ⟨x, hx, rfl⟩
  exact (capInclusion_edist_le I R U hU hd hc i (R i).tip x).trans (hclosed hx)

end PoincareConjecture.Surgery.Terminal.Gluing

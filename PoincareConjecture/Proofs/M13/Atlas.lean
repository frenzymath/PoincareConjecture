import PoincareConjecture.Definitions.M13AtlasRescaling
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false

open scoped ContDiff Topology

universe u

namespace PoincareConjecture.M13

noncomputable def timeHomeomorph (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I : SpacetimeInterval) : I.domain ≃ₜ (parabolicInterval Q hQ a I).domain where
  toFun t := ⟨parabolicTime Q a t.val,
    (parabolicTime_mem_parabolicInterval_iff Q hQ a I t.val).2 t.property⟩
  invFun s := ⟨parabolicTimeInv Q a s.val,
    (mem_parabolicInterval_iff Q hQ a I s.val).1 s.property⟩
  left_inv t := Subtype.ext (parabolicTimeInv_parabolicTime Q hQ a t.val)
  right_inv s := Subtype.ext (parabolicTime_parabolicTimeInv Q hQ a s.val)
  continuous_toFun :=
    (continuous_const.mul (continuous_subtype_val.sub continuous_const)).subtype_mk _
  continuous_invFun :=
    (continuous_const.add (continuous_subtype_val.div_const Q)).subtype_mk _

theorem interval_relatively_open (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (I J : SpacetimeInterval)
    (h : ∃ U : Set ℝ, IsOpen U ∧ J.domain = I.domain ∩ U) :
    ∃ U : Set ℝ, IsOpen U ∧
      (parabolicInterval Q hQ a J).domain = (parabolicInterval Q hQ a I).domain ∩ U := by
  rcases h with ⟨U, hU, hJ⟩
  refine ⟨parabolicTimeInv Q a ⁻¹' U,
    hU.preimage (continuous_const.add (continuous_id.div_const Q)), ?_⟩
  ext s
  simp only [Set.mem_inter_iff, Set.mem_preimage, mem_parabolicInterval_iff, hJ]

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}

noncomputable def rescaledBox (b : AdaptedMetricBox n X time I)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    AdaptedMetricBox n X (fun p ↦ parabolicTime Q a (time p))
      (parabolicInterval Q hQ a I) where
  interval := parabolicInterval Q hQ a b.interval
  spatial := b.spatial
  spatial_nonempty := b.spatial_nonempty
  interval_relatively_open :=
    interval_relatively_open Q hQ a I b.interval b.interval_relatively_open
  toSpacetime p := b.toSpacetime ((timeHomeomorph Q hQ a b.interval).symm p.1, p.2)
  openEmbedding := b.openEmbedding.comp
    (((timeHomeomorph Q hQ a b.interval).symm.prodCongr
      (Homeomorph.refl b.spatial)).isOpenEmbedding)
  time_toSpacetime p := by
    rw [b.time_toSpacetime]
    exact parabolicTime_parabolicTimeInv Q hQ a p.1.val
  metric p := Q • b.metric (parabolicTimeInv Q a p.1, p.2)
  metric_smooth := by
    apply ContDiffOn.const_smul Q
    apply b.metric_smooth.comp
      ((contDiff_const.add (contDiff_fst.div_const Q)).prodMk contDiff_snd).contDiffOn
    intro p hp
    exact ⟨(mem_parabolicInterval_iff Q hQ a b.interval p.1).1 hp.1, hp.2⟩
  metric_symm t ht x hx v w := by
    change Q * b.metric (parabolicTimeInv Q a t, x) v w =
      Q * b.metric (parabolicTimeInv Q a t, x) w v
    rw [b.metric_symm _ ((mem_parabolicInterval_iff Q hQ a b.interval t).1 ht) x hx]
  metric_pos t ht x hx v hv :=
    mul_pos hQ (b.metric_pos _
      ((mem_parabolicInterval_iff Q hQ a b.interval t).1 ht) x hx v hv)

noncomputable def rescaledTransition {b c : AdaptedMetricBox n X time I}
    {t : ℝ} {x y : EuclideanSpace ℝ (Fin n)}
    (θ : AdaptedMetricTransition b c t x y) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    AdaptedMetricTransition (rescaledBox b Q hQ a) (rescaledBox c Q hQ a)
      (parabolicTime Q a t) x y where
  interval := parabolicInterval Q hQ a θ.interval
  interval_relatively_open :=
    interval_relatively_open Q hQ a I θ.interval θ.interval_relatively_open
  interval_subset_left := Set.image_mono θ.interval_subset_left
  interval_subset_right := Set.image_mono θ.interval_subset_right
  time_mem := (parabolicTime_mem_parabolicInterval_iff Q hQ a θ.interval t).2 θ.time_mem
  coordinateChange := θ.coordinateChange
  source_subset := θ.source_subset
  target_subset := θ.target_subset
  source_mem := θ.source_mem
  map_marked := θ.map_marked
  smooth := θ.smooth
  symm_smooth := θ.symm_smooth
  box_eq s hs z hz := θ.box_eq (parabolicTimeInv Q a s)
    ((mem_parabolicInterval_iff Q hQ a θ.interval s).1 hs) z hz
  metric_eq s hs z hz v w := by
    change Q * b.metric (parabolicTimeInv Q a s, z) v w =
      Q * c.metric (parabolicTimeInv Q a s, θ.coordinateChange z)
        (fderiv ℝ θ.coordinateChange z v) (fderiv ℝ θ.coordinateChange z w)
    rw [θ.metric_eq _ ((mem_parabolicInterval_iff Q hQ a θ.interval s).1 hs) z hz]

noncomputable def rescaledAtlas (A : AdaptedMetricAtlas n X)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) : AdaptedMetricAtlas n X where
  time p := parabolicTime Q a (A.time p)
  interval := parabolicInterval Q hQ a A.interval
  time_continuous := continuous_const.mul (A.time_continuous.sub continuous_const)
  time_range := by
    change Set.range (parabolicTime Q a ∘ A.time) =
      parabolicTime Q a '' A.interval.domain
    rw [Set.range_comp, A.time_range]
  box_index := A.box_index
  box b := rescaledBox (A.box b) Q hQ a
  box_covers p := by
    rcases A.box_covers p with ⟨b, ⟨t, x⟩, hp⟩
    refine ⟨b, ((timeHomeomorph Q hQ a (A.box b).interval) t, x), ?_⟩
    change (A.box b).toSpacetime
      ((timeHomeomorph Q hQ a (A.box b).interval).symm
        ((timeHomeomorph Q hQ a (A.box b).interval) t), x) = p
    simpa only [Homeomorph.symm_apply_apply] using hp
  transitions b c t hb hc x y he := by
    let hb' := (mem_parabolicInterval_iff Q hQ a (A.box b).interval t).1 hb
    let hc' := (mem_parabolicInterval_iff Q hQ a (A.box c).interval t).1 hc
    obtain ⟨θ⟩ := A.transitions b c (parabolicTimeInv Q a t) hb' hc' x y he
    simpa only [parabolicTime_parabolicTimeInv Q hQ a t] using
      (Nonempty.intro (rescaledTransition θ Q hQ a))

noncomputable def atlasRescaling (A : AdaptedMetricAtlas n X)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) : ParabolicAtlasRescaling A Q hQ a where
  atlas := rescaledAtlas A Q hQ a
  time_eq := rfl
  interval_eq := rfl
  box_index_eq := rfl
  box_interval _ := rfl
  box_spatial _ := rfl
  box_map b t x := by
    change (A.box b).toSpacetime
      ((timeHomeomorph Q hQ a (A.box b).interval).symm
        ((timeHomeomorph Q hQ a (A.box b).interval) t), x) = _
    rw [Homeomorph.symm_apply_apply]
  metric_eq _ _ _ _ _ := rfl
  transition_transport _ _ _ _ _ θ := ⟨rescaledTransition θ Q hQ a, rfl, rfl⟩

end PoincareConjecture.M13

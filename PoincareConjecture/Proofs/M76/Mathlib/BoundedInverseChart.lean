import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.MetricSpace.Antilipschitz









set_option autoImplicit false

open Set Topology
open scoped NNReal

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Nonempty X]
  {f : X → Y} {S : Set X} {K : ℝ≥0}




theorem ContinuousOn.exists_openPartialHomeomorph_of_antilipschitz
    (hf : ContinuousOn f S) (hS : IsOpen S) (himage : IsOpen (f '' S))
    (hbound : AntilipschitzWith K (S.domRestrict f)) :
    ∃ e : OpenPartialHomeomorph X Y,
      (e : X → Y) = f ∧ e.source = S ∧ e.target = f '' S := by
  have hopen : IsOpen (range (S.domRestrict f)) := by
    have he : range (S.domRestrict f) = f '' S := by ext y; simp
    rw [he]
    exact himage
  have hemb : IsOpenEmbedding (S.domRestrict f) :=
    ⟨hbound.isEmbedding hf.domRestrict, hopen⟩
  have hinj : InjOn f S := injOn_iff_injective.mpr hbound.injective
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hinj.toPartialEquiv f S) hf hemb.isOpenMap hS, rfl, rfl, rfl⟩





theorem Continuous.exists_openPartialHomeomorph_of_inverse_bound
    (hf : Continuous f) {a : X} (hS : S ∈ 𝓝 a)
    (hbound : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ K * dist (f x) (f y))
    (himage : f a ∈ interior (f '' S)) {V : Set X} (hV : V ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph X Y, (e : X → Y) = f ∧
      a ∈ e.source ∧ e.source ⊆ S ∩ V := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hS hV)
  let δ : ℝ := r / ((K : ℝ) + 1)
  have hK : 0 < (K : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos hr hK
  let T := Metric.ball (f a) δ ∩ interior (f '' S)
  have hT : IsOpen T := Metric.isOpen_ball.inter isOpen_interior
  have haT : f a ∈ T := ⟨Metric.mem_ball_self hδ, himage⟩
  let U := Metric.ball a r ∩ f ⁻¹' T
  have hU : IsOpen U := Metric.isOpen_ball.inter (hT.preimage hf)
  have haU : a ∈ U := ⟨Metric.mem_ball_self hr, haT⟩
  have hUSV : U ⊆ S ∩ V := fun _ hx => hball hx.1
  have hUS : U ⊆ S := hUSV.trans inter_subset_left
  have himageU : f '' U = T := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      obtain ⟨x, hxS, rfl⟩ := interior_subset hy.2
      refine ⟨x, ⟨?_, hy⟩, rfl⟩
      have hdist : dist (f x) (f a) < δ := hy.1
      change dist x a < r
      calc
        dist x a ≤ K * dist (f x) (f a) := hbound x hxS a (mem_of_mem_nhds hS)
        _ ≤ ((K : ℝ) + 1) * dist (f x) (f a) := by
          nlinarith [show 0 ≤ dist (f x) (f a) from dist_nonneg]
        _ < ((K : ℝ) + 1) * δ := mul_lt_mul_of_pos_left hdist hK
        _ = r := mul_div_cancel₀ _ hK.ne'
  have hanti : AntilipschitzWith K (U.domRestrict f) :=
    AntilipschitzWith.of_le_mul_dist (fun x y =>
      hbound x (hUS x.property) y (hUS y.property))
  obtain ⟨e, he, hsource, _⟩ := hf.continuousOn.exists_openPartialHomeomorph_of_antilipschitz
    hU (himageU ▸ hT) hanti
  exact ⟨e, he, hsource ▸ haU, hsource ▸ hUSV⟩

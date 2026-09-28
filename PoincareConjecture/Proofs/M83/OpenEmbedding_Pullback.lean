import PoincareConjecture.Proofs.M02.Topology.PositiveThreeAtlas











set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology

universe u v

namespace PoincareConjecture.Proofs.M83

open PoincareConjecture.Proofs.M02.Topology




def positiveThreeAtlasOpenEmbedding
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] (f : X → Y) (hf : _root_.Topology.IsOpenEmbedding f)
    (A : PositiveThreeAtlas Y) : PositiveThreeAtlas X := by
  let E := EuclideanSpace Real (Fin 3)
  let j := hf.toOpenPartialHomeomorph f
  let I := {e : OpenPartialHomeomorph Y E // e ∈ A.charts.atlas}
  let c (e : I) := j.trans e.1
  have hj : ∀ x : X, x ∈ j.source := fun _ => by simp [j]
  have hjf : ∀ x : X, j x = f x := fun _ => rfl
  let chosen (x : X) : I :=
    ⟨A.charts.chartAt (f x), A.charts.chart_mem_atlas (f x)⟩
  refine ⟨{
    atlas := range c
    chartAt := fun x => c (chosen x)
    mem_chart_source := ?_
    chart_mem_atlas := fun x => ⟨chosen x, rfl⟩ }, ?_⟩
  · intro x
    exact ⟨hj x, A.charts.mem_chart_source (f x)⟩
  · intro a b ha hb x hx
    obtain ⟨e, rfl⟩ := ha
    obtain ⟨e', rfl⟩ := hb
    have hxe : f x ∈ e.1.source := hx.1.2
    have hxe' : f x ∈ e'.1.source := hx.2.2
    have htarget : e.1.symm (e.1 (f x)) ∈ j.target := by
      rw [e.1.left_inv hxe]
      exact j.map_source (hj x)
    have hnhds : ∀ᶠ z in 𝓝 (e.1 (f x)), e.1.symm z ∈ j.target :=
      (e.1.symm.continuousAt (e.1.map_source hxe))
        (j.open_target.mem_nhds htarget)
    have heq : (fun z : E => c e' ((c e).symm z)) =ᶠ[𝓝 (e.1 (f x))]
        (fun z : E => e'.1 (e.1.symm z)) := by
      filter_upwards [hnhds] with z hz
      change e'.1 (j (j.symm (e.1.symm z))) = e'.1 (e.1.symm z)
      rw [j.right_inv hz]
    change 0 < (fderiv Real (fun z : E => c e' ((c e).symm z))
      (e.1 (f x))).toLinearMap.det
    rw [heq.fderiv_eq]
    exact A.positive_transition e.1 e'.1 e.2 e'.2 (f x) ⟨hxe, hxe'⟩

end PoincareConjecture.Proofs.M83

import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularSurfaceChart
import Mathlib.Topology.Connected.LocallyConnected













set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {M : Type*} [TopologicalSpace M]



noncomputable def levelSliceChart (f : M → ℝ) (t : ℝ)
    (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (hcoord : ∀ y ∈ e.source, (e y).2 = f y) (x : {y // f y = t}) :
    OpenPartialHomeomorph {y // f y = t} ℝ := by
  classical
  let j : ℝ → {y // f y = t} := fun s =>
    if hs : (s, t) ∈ e.target then
      ⟨e.symm (s, t), (hcoord _ (e.map_target hs)).symm.trans
        (congrArg Prod.snd (e.right_inv hs))⟩
    else x
  have hj (s : ℝ) (hs : (s, t) ∈ e.target) : (j s).1 = e.symm (s, t) := by
    simp only [j, dif_pos hs]
  have hpair (p : {y // f y = t}) (hp : p.1 ∈ e.source) :
      ((e p.1).1, t) = e p.1 :=
    Prod.ext rfl ((hcoord p.1 hp).trans p.2).symm
  refine
    { toFun := fun p => (e p.1).1
      invFun := j
      source := {p | p.1 ∈ e.source}
      target := {s | (s, t) ∈ e.target}
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage (continuous_id.prodMk continuous_const) }
  · intro p hp
    change ((e p.1).1, t) ∈ e.target
    rw [hpair p hp]
    exact e.map_source hp
  · intro s hs
    change (j s).1 ∈ e.source
    rw [hj s hs]
    exact e.map_target hs
  · intro p hp
    have ht : ((e p.1).1, t) ∈ e.target := by
      rw [hpair p hp]
      exact e.map_source hp
    apply Subtype.ext
    change (j (e p.1).1).1 = p.1
    rw [hj _ ht, hpair p hp, e.left_inv hp]
  · intro s hs
    rw [hj s hs, e.right_inv hs]
  · exact (e.continuousOn.comp continuous_subtype_val.continuousOn
      (fun _ hp => hp)).fst
  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (e.continuousOn_symm.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ hs => hs)).congr
        (fun s hs => hj s hs)



@[simp] theorem levelSliceChart_source (f : M → ℝ) (t : ℝ)
    (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (hcoord : ∀ y ∈ e.source, (e y).2 = f y) (x : {y // f y = t}) :
    (levelSliceChart f t e hcoord x).source = {p | p.1 ∈ e.source} := rfl


@[simp] theorem levelSliceChart_apply (f : M → ℝ) (t : ℝ)
    (e : OpenPartialHomeomorph M (ℝ × ℝ))
    (hcoord : ∀ y ∈ e.source, (e y).2 = f y) (x p : {y // f y = t}) :
    levelSliceChart f t e hcoord x p = (e p.1).1 := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]



theorem exists_regular_level_line_chart (hdim : Module.finrank ℝ E = 2)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (t : ℝ)
    (hreg : ∀ y, f y = t → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f y ≠ 0)
    (x : {y // f y = t}) :
    ∃ e : OpenPartialHomeomorph {y // f y = t} ℝ, x ∈ e.source := by
  obtain ⟨e, hxe, _, _, hcoord⟩ :=
    exists_surface_regular_chart hdim f hf x.1 (hreg x.1 x.2)
  exact ⟨levelSliceChart f t e hcoord x, hxe⟩



theorem locallyConnected_regular_surface_level (hdim : Module.finrank ℝ E = 2)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (t : ℝ)
    (hreg : ∀ y, f y = t → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f y ≠ 0) :
    LocallyConnectedSpace {y // f y = t} := by
  classical
  let C : {y // f y = t} → OpenPartialHomeomorph {y // f y = t} ℝ :=
    fun x => (exists_regular_level_line_chart hdim f hf t hreg x).choose
  let : ChartedSpace ℝ {y // f y = t} :=
    { atlas := univ
      chartAt := C
      mem_chart_source := fun x =>
        (exists_regular_level_line_chart hdim f hf t hreg x).choose_spec
      chart_mem_atlas := fun _ => mem_univ _ }
  exact ChartedSpace.locallyConnectedSpace ℝ _



theorem finite_regular_surface_level_components [CompactSpace M]
    (hdim : Module.finrank ℝ E = 2)
    (f : M → ℝ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (t : ℝ)
    (hreg : ∀ y, f y = t → mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f y ≠ 0) :
    Finite (ConnectedComponents {y // f y = t}) := by
  let : LocallyConnectedSpace {y // f y = t} :=
    locallyConnected_regular_surface_level hdim f hf t hreg
  let : CompactSpace {y // f y = t} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  infer_instance

end PoincareConjecture.M25.Topology3D

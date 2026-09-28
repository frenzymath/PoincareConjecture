import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Basic
import Mathlib.Topology.LocalAtTarget

noncomputable section
set_option autoImplicit false

open Set Topology TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.GeneralizedRicciFlowData

theorem isEmbedding_of_local_box {G : GeneralizedRicciFlowData.{u}}
    {X : Type v} [TopologicalSpace X] {J : Set ℝ} {origin scale : ℝ}
    (hscale : 0 < scale) (htime : ∀ s ∈ J, origin + s / scale ∈ G.interval)
    (f : ∀ s : ℝ, s ∈ J → X → (G.slice (origin + s / scale)).carrier)
    (hlocal : ∀ (s : ℝ) (_hs : s ∈ J), ∃ b : G.box_index,
      ∃ _hb : origin + s / scale ∈ (G.box b).interval,
      ∃ y : X → (G.box b).carrier.carrier, IsEmbedding y ∧
        ∀ t ht (htb : origin + t / scale ∈ (G.box b).interval) x,
          f t ht x = (G.box b).forward (origin + t / scale) htb (y x)) :
    IsEmbedding (fun p : J × X =>
      (⟨origin + p.1.val / scale, f p.1.val p.1.property p.2⟩ : G.point)) := by
  classical
  choose b hb y hy heq using (fun s : J => hlocal s.val s.property)
  choose I hI hrel using (fun s : J => (G.box (b s)).relatively_open)
  let clock : ℝ → ℝ := fun t => origin + t / scale
  have hclock : IsEmbedding clock := by
    apply IsEmbedding.of_leftInverse
      (f := fun t : ℝ => (t - origin) * scale)
      (g := clock)
    · intro t
      dsimp [clock]
      rw [add_sub_cancel_left, div_mul_cancel₀ _ (ne_of_gt hscale)]
    · fun_prop
    · exact continuous_const.add (continuous_id.div_const scale)
  let K : J → Set J := fun s => {t | clock t.val ∈ I s}
  have hK (s : J) : IsOpen (K s) :=
    (hI s).preimage (hclock.continuous.comp continuous_subtype_val)
  have hself (s : J) : s ∈ K s := (hrel s ▸ hb s).2
  let V : J → Type _ := fun s => K s × X
  let iV : ∀ s : J, V s → J × X := fun _ p => (p.1.val, p.2)
  have hiV (s : J) : IsOpenEmbedding (iV s) :=
    (hK s).isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
  let spaceMap : J × X → G.point := fun p =>
    ⟨clock p.1.val, f p.1.val p.1.property p.2⟩
  have hV (s : J) : IsEmbedding (spaceMap ∘ iV s) := by
    let timeMap : K s → (G.box (b s)).interval := fun t =>
      ⟨clock t.val.val, (hrel s).symm ▸ ⟨htime t.val.val t.val.property, t.property⟩⟩
    have ht : IsEmbedding timeMap :=
      ((hclock.comp IsEmbedding.subtypeVal).comp IsEmbedding.subtypeVal).codRestrict _ _
    let boxMap : (G.box (b s)).interval × (G.box (b s)).carrier.carrier → G.point :=
      fun p => ⟨p.1.val, (G.box (b s)).forward p.1.val p.1.property p.2⟩
    have hfun : spaceMap ∘ iV s = boxMap ∘ Prod.map timeMap (y s) := by
      funext p
      exact Sigma.ext rfl (heq_of_eq (heq s p.1.val.val p.1.val.property
        (timeMap p.1).property p.2))
    rw [hfun]
    exact (G.box_openEmbedding (b s)).isEmbedding.comp (ht.prodMap (hy s))
  have hf : Continuous spaceMap := by
    apply continuous_def.mpr
    intro O hO
    have hpre : spaceMap ⁻¹' O =
        ⋃ s : J, iV s '' ((spaceMap ∘ iV s) ⁻¹' O) := by
      ext p
      constructor
      · intro hp
        exact mem_iUnion.mpr ⟨p.1, ⟨(⟨p.1, hself p.1⟩, p.2), hp, rfl⟩⟩
      · intro hp
        obtain ⟨s, q, hq, rfl⟩ := mem_iUnion.mp hp
        exact hq
    rw [hpre]
    exact isOpen_iUnion fun s => (hiV s).isOpenMap _ (hO.preimage (hV s).continuous)
  let target : J → Opens G.point := fun s =>
    ⟨Sigma.fst ⁻¹' I s, (hI s).preimage G.time_continuous⟩
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range spaceMap hf target ?_ V iV
    (fun s => (hiV s).continuous) ?_ hV
  · rintro _ ⟨p, rfl⟩
    exact (le_iSup target p.1) (hself p.1)
  · intro s p hp
    exact ⟨(⟨p.1, hp⟩, p.2), rfl⟩

end PoincareConjecture.GeneralizedRicciFlowData

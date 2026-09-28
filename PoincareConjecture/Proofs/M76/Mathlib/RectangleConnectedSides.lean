import PoincareConjecture.Proofs.M76.Mathlib.RectangleCollarSides
import Mathlib.Topology.Connected.TotallyDisconnected










set_option autoImplicit false

open Set

namespace Homeomorph

variable {X : Type*} [TopologicalSpace X]





theorem exists_rectangle_side_of_height_interval
    {α β : ℝ} (hαβ : α ≤ β) {T S : Set X}
    (G : (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ)) ≃ₜ T)
    (d : Icc α β ≃ₜ S) (hST : S ⊆ T) (A : X → ℝ)
    (hG : ∀ p, A (G p) = (p : ℝ × ℝ).2)
    (hd : ∀ t, A (d t) = (t : ℝ))
    (hside : ∀ t,
      (G.symm ⟨d t, hST (d t).property⟩ : ℝ × ℝ).1 = 0 ∨
      (G.symm ⟨d t, hST (d t).property⟩ : ℝ × ℝ).1 = 1) :
    ∃ k : Icc (0 : ℝ) 1, ((k : ℝ) = 0 ∨ (k : ℝ) = 1) ∧
      ∀ t : Icc α β,
        (G ⟨(k, t), ⟨k.property, t.property⟩⟩ : X) = d t := by
  let : PreconnectedSpace (Icc α β) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  let f : Icc α β → ℝ := fun t =>
    (G.symm ⟨d t, hST (d t).property⟩ : ℝ × ℝ).1
  have hf : Continuous f :=
    continuous_fst.comp (continuous_subtype_val.comp
      (G.symm.continuous.comp
        ((continuous_subtype_val.comp d.continuous).subtype_mk _)))
  have hmaps : MapsTo f univ ({0, 1} : Set ℝ) := fun t _ => hside t
  let a : Icc α β := ⟨α, le_rfl, hαβ⟩
  let p₀ := G.symm ⟨d a, hST (d a).property⟩
  let k : Icc (0 : ℝ) 1 := ⟨(p₀ : ℝ × ℝ).1, p₀.property.1⟩
  have hconst (t : Icc α β) : f t = f a :=
    isPreconnected_univ.constant_of_mapsTo (Set.toFinite ({0, 1} : Set ℝ)).isDiscrete
      hf.continuousOn hmaps (mem_univ t) (mem_univ a)
  refine ⟨k, hside a, ?_⟩
  intro t
  let p := G.symm ⟨d t, hST (d t).property⟩
  have hp : (G p : X) = d t := congrArg Subtype.val (G.apply_symm_apply _)
  have hpheight : (p : ℝ × ℝ).2 = (t : ℝ) :=
    (hG p).symm.trans ((congrArg A hp).trans (hd t))
  have heq : p = ⟨(k, t), ⟨k.property, t.property⟩⟩ :=
    Subtype.ext (Prod.ext (hconst t) hpheight)
  rwa [heq] at hp

end Homeomorph

namespace Homeomorph

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePL.exists_bottom_normalized_rectangle_chart_with_overlaps
    {α β : ℝ} (hαβ : α < β) {T : Set E}
    {G : (Icc (0 : ℝ) 1 ×ˢ Icc α β : Set (ℝ × ℝ)) ≃ₜ T}
    (hG : G.IsFinitePL) (A : E → ℝ)
    (hheight : ∀ p, A (G p) = (p : ℝ × ℝ).2)
    (S : ι → Set E)
    (hover : ∀ i, (T ∩ S i).Nonempty →
      ∃ d : Icc α β ≃ₜ (T ∩ S i : Set E), ∀ t, A (d t) = (t : ℝ))
    (hboundary : ∀ i p, (G p : E) ∈ S i →
      (p : ℝ × ℝ).1 = 0 ∨ (p : ℝ × ℝ).1 = 1) :
    ∃ C : ((T ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ T,
      C.IsFinitePL ∧ (∀ p, A (C p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ T ∩ {x | A x = α}),
        (C ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) = x) ∧
      ∀ i (p : ((T ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ))),
        (C p : E) ∈ S i ↔ (p : E × ℝ).1 ∈ S i := by
  classical
  let J := {i : ι // (T ∩ S i).Nonempty}
  have hex (j : J) : ∃ d : Icc α β ≃ₜ (T ∩ S j.val : Set E),
      ∀ t, A (d t) = (t : ℝ) := hover j.val j.property
  choose d hd using hex
  have hside (j : J) : ∃ k : Icc (0 : ℝ) 1,
      ((k : ℝ) = 0 ∨ (k : ℝ) = 1) ∧ ∀ t : Icc α β,
        (G ⟨(k, t), ⟨k.property, t.property⟩⟩ : E) = d j t := by
    apply exists_rectangle_side_of_height_interval hαβ.le G (d j)
      inter_subset_left A hheight (hd j)
    intro t
    apply hboundary j.val
    simpa only [G.apply_symm_apply] using (d j t).property.2
  choose k _ hk using hside
  obtain ⟨C, hC, hCA, hbase, hmem⟩ :=
    hG.exists_bottom_normalized_rectangle_chart_with_sides
      hαβ A hheight (fun j : J => T ∩ S j.val) k d hk
  refine ⟨C, hC, hCA, hbase, ?_⟩
  intro i p
  constructor
  · intro hp
    let j : J := ⟨i, ⟨C p, (C p).property, hp⟩⟩
    exact ((hmem j p).mp ⟨(C p).property, hp⟩).2
  · intro hp
    let j : J := ⟨i, ⟨(p : E × ℝ).1, p.property.1.1, hp⟩⟩
    exact ((hmem j p).mpr ⟨p.property.1.1, hp⟩).2

end Homeomorph

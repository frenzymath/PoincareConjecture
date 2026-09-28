import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.CompressionCapGeometry
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimLoop

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem outer_lateral_point_mem_component_sdiff_cap
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F Fnew S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (hcomponent : ∀ y ∈ S, connectedComponentIn Fnew y = S)
    (b : Bool) (hcap : P.capDisk b ⊆ S) :
    P.map ((Dehn.squareRimBase : V2), if b then (3 / 4 : ℝ) else -(3 / 4)) ∈
      S \ P.capDisk b := by
  let height : Icc (0 : ℝ) 1 → ℝ :=
    fun t => if b then 1 / 2 + t / 4 else -(1 / 2 + t / 4)
  have hheight (t : Icc (0 : ℝ) 1) : height t ∈ Icc (-1 : ℝ) 1 := by
    have h0 := t.property.1
    have h1 := t.property.2
    cases b <;> simp only [height, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith
  let coords : Icc (0 : ℝ) 1 → (D ×ˢ Icc (-1 : ℝ) 1 : Set (V2 × ℝ)) :=
    fun t => ⟨(Dehn.squareRimBase, height t),
      sphere_subset_closedBall Dehn.squareRimBase.property, hheight t⟩
  have hc : Continuous coords := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    dsimp [height]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  let path : Icc (0 : ℝ) 1 → X := fun t => P.map (coords t)
  have hp : Continuous path := P.embedding.continuous.comp hc
  have hpath : range path ⊆ Fnew := by
    rintro y ⟨t, rfl⟩
    apply hnew.symm.subset
    refine Or.inl ⟨(P.protected_frontier_iff hcut hsmall _ (coords t).property).mpr
      Dehn.squareRimBase.property, ?_⟩
    rintro ⟨w, hw, heq⟩
    have hwfull : w ∈ D ×ˢ Icc (-1 : ℝ) 1 :=
      ⟨hw.1, by linarith [hw.2.1], by linarith [hw.2.2]⟩
    have ht := congrArg Prod.snd (P.injective hwfull (coords t).property heq)
    change w.2 = height t at ht
    have h0 := t.property.1
    cases b <;> simp only [height, Bool.false_eq_true, ↓reduceIte] at ht <;>
      linarith [hw.2.1, hw.2.2]
  let zero : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let one : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hzero : path zero ∈ S := by
    apply hcap
    refine ⟨(Dehn.squareRimBase, height zero), ?_, rfl⟩
    refine ⟨sphere_subset_closedBall Dehn.squareRimBase.property, ?_⟩
    cases b <;> simp [height, zero]
  have hrange : range path ⊆ S :=
    ((isConnected_range hp).isPreconnected.subset_connectedComponentIn
      (mem_range_self zero) hpath).trans (hcomponent (path zero) hzero).subset
  have hone : path one =
      P.map ((Dehn.squareRimBase : V2), if b then (3 / 4 : ℝ) else -(3 / 4)) := by
    dsimp [path, coords, height, one]
    congr 1
    cases b <;> norm_num
  rw [← hone]
  refine ⟨hrange (mem_range_self one), ?_⟩
  rintro ⟨w, hw, heq⟩
  have htcap : w.2 = if b then (1 / 2 : ℝ) else -(1 / 2) := hw.2
  have hwfull : w ∈ D ×ˢ Icc (-1 : ℝ) 1 := by
    refine ⟨hw.1, ?_⟩
    rw [htcap]
    cases b <;> norm_num
  have ht := congrArg Prod.snd (P.injective hwfull (coords one).property heq)
  change w.2 = height one at ht
  cases b <;> simp [height, one] at htcap ht <;> linarith

theorem cap_complement_nonempty
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L U F Fnew S : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j)
    (hcut : U ∩ frontier L = F)
    (hsmall : MapsTo P.map (D ×ˢ Icc (-1 : ℝ) 1) U)
    (hnew : Fnew = (F \ P.openStrip) ∪ P.endDisks)
    (hcomponent : ∀ y ∈ S, connectedComponentIn Fnew y = S)
    (b : Bool) (hcap : P.capDisk b ⊆ S) :
    (S \ P.capDisk b).Nonempty :=
  ⟨_, P.outer_lateral_point_mem_component_sdiff_cap hcut hsmall hnew hcomponent b hcap⟩

end PoincareConjecture.M76.OriginalDiskProduct

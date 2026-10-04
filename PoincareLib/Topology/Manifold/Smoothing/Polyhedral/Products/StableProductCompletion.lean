import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Products.PLFiberCompression
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Completing a stable immersion on its product region

An immersion of a thin cylinder which is a product over an
open base region extends there to the unit-height cylinder.
An exact PL fiber homeomorphism then compresses the remaining
fibers into the thin part while retaining a prescribed product
core. See the Edwards/Rushing source lead and its independently
reconstructed normalization in M76 derivation 270, for
Hamilton 1976, p. 66.
-/

set_option autoImplicit false

open Set

namespace IsLocalHomeomorphOn

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Local homeomorphisms on two open domains which agree on
their overlap have an actual pasted local homeomorphism.
The statement retains its values on both entire domains.
See M76 derivation 270, stable product completion. -/
theorem exists_union {f g : X → Y} {U V : Set X}
    (hf : IsLocalHomeomorphOn f U) (hg : IsLocalHomeomorphOn g V)
    (hU : IsOpen U) (hV : IsOpen V) (heq : EqOn f g (U ∩ V)) :
    ∃ F : X → Y, IsLocalHomeomorphOn F (U ∪ V) ∧
      EqOn F f U ∧ EqOn F g V := by
  classical
  let F : X → Y := fun x => if x ∈ U then f x else g x
  have hFf : EqOn F f U := fun x hx => by simp only [F, if_pos hx]
  have hFg : EqOn F g V := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact (hFf hxU).trans (heq ⟨hxU, hx⟩)
    · simp only [F, if_neg hxU]
  refine ⟨F, IsLocalHomeomorphOn.mk F (U ∪ V) ?_, hFf, hFg⟩
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨e, hxe, he⟩ := hf x hx
    refine ⟨e.restr U, ⟨hxe, hU.interior_eq.symm ▸ hx⟩, ?_⟩
    intro y hy
    exact (hFf (interior_subset hy.2)).trans (congrFun he y)
  · obtain ⟨e, hxe, he⟩ := hg x hx
    refine ⟨e.restr V, ⟨hxe, hV.interior_eq.symm ▸ hx⟩, ?_⟩
    intro y hy
    exact (hFg (interior_subset hy.2)).trans (congrFun he y)

/-- Taking a product with an identity retains the actual
local homeomorphism on the product domain. No separation
hypothesis on either factor is needed. See M76 derivation 270. -/
theorem prod_id {Z : Type*} [TopologicalSpace Z] {f : X → Y} {U : Set X}
    (hf : IsLocalHomeomorphOn f U) :
    IsLocalHomeomorphOn (fun z : X × Z => (f z.1, z.2)) (U ×ˢ univ) := by
  intro z hz
  obtain ⟨e, hze, he⟩ := hf z.1 hz.1
  refine ⟨e.prod (OpenPartialHomeomorph.refl Z), ⟨hze, mem_univ _⟩, ?_⟩
  funext p
  exact Prod.ext (congrFun he p.1) rfl

end IsLocalHomeomorphOn

namespace PLFiberCompression

/-- A thin-cylinder immersion with an actual open product
region extends to full unit-height fibers after compression,
retaining the exact product on the prescribed width-one core.
All domain and image bounds are explicit. See M76 derivation
270, stable product completion. -/
theorem exists_stable_product_completion_with_formula {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U K : Set X) (hU : IsOpen U) (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (h : X × ℝ → Y × ℝ) (g : X → Y)
    (hh : IsLocalHomeomorphOn h (univ ×ˢ Ioo (-delta) delta))
    (hg : IsLocalHomeomorphOn g U)
    (hheight : MapsTo h (univ ×ˢ Ioo (-delta) delta) (univ ×ˢ Ioo (-1) 1))
    (hprod : EqOn h (fun z => (g z.1, z.2)) (U ×ˢ Ioo (-delta) delta))
    (w : X → ℝ) (hc : Continuous w) (hw : ∀ x, w x ∈ Icc 0 1)
    (hout : ∀ x, x ∉ U → w x = 0) (hcore : ∀ x ∈ K, w x = 1) :
    ∃ F B : X × ℝ → Y × ℝ,
      IsLocalHomeomorphOn F (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo F (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      EqOn F (fun z => (g z.1, z.2)) (K ×ˢ Ioo (-1) 1) ∧
      F = B ∘ homeomorph delta hd w (fun x => (hw x).1) hc ∧
      EqOn B h (univ ×ˢ Ioo (-delta) delta) ∧
      EqOn B (fun z => (g z.1, z.2)) (U ×ˢ Ioo (-1) 1) ∧
      MapsTo (homeomorph delta hd w (fun x => (hw x).1) hc)
        (univ ×ˢ Ioo (-1) 1)
        ((univ ×ˢ Ioo (-delta) delta) ∪ (U ×ˢ Ioo (-1) 1)) := by
  let T : Set (X × ℝ) := univ ×ˢ Ioo (-delta) delta
  let P : Set (X × ℝ) := U ×ˢ Ioo (-1) 1
  let V : Set (X × ℝ) := univ ×ˢ Ioo (-1) 1
  let G : X × ℝ → Y × ℝ := fun z => (g z.1, z.2)
  have hG : IsLocalHomeomorphOn G P :=
    hg.prod_id.mono (fun _ hz => ⟨hz.1, mem_univ _⟩)
  have heq : EqOn h G (T ∩ P) := fun _ hz => hprod ⟨hz.2.1, hz.1.2⟩
  obtain ⟨F, hF, hFh, hFG⟩ := hh.exists_union hG
    (isOpen_univ.prod isOpen_Ioo) (hU.prod isOpen_Ioo) heq
  let C := homeomorph delta hd w (fun x => (hw x).1) hc
  have hCV : MapsTo C V (T ∪ P) := by
    intro z hz
    by_cases hzU : z.1 ∈ U
    · exact Or.inr ⟨hzU, value_mem_unit_interval hd hd1 (hw z.1).1 (hw z.1).2 hz.2⟩
    · apply Or.inl
      refine ⟨mem_univ _, ?_⟩
      change value delta (w z.1) z.2 ∈ Ioo (-delta) delta
      rw [hout z.1 hzU, value_zero_width]
      constructor <;> nlinarith [mul_pos hd (show 0 < z.2 + 1 by linarith [hz.2.1]),
        mul_pos hd (show 0 < 1 - z.2 by linarith [hz.2.2])]
  have hFV : MapsTo F (T ∪ P) (univ ×ˢ Ioo (-1) 1) := by
    intro z hz
    rcases hz with hz | hz
    · rw [hFh hz]
      exact hheight hz
    · rw [hFG hz]
      exact ⟨mem_univ _, hz.2⟩
  refine ⟨F ∘ C, F, hF.comp C.isLocalHomeomorph.isLocalHomeomorphOn hCV,
    fun _ hz => hFV (hCV hz), ?_, rfl, hFh, hFG, hCV⟩
  intro z hz
  have hzU : z.1 ∈ U := by
    by_contra hn
    have he := (hout z.1 hn).symm.trans (hcore z.1 hz.1)
    norm_num at he
  have hCz : C z = z := by
    apply Prod.ext
    · rfl
    · change value delta (w z.1) z.2 = z.2
      rw [hcore z.1 hz.1]
      exact value_of_mem ⟨hz.2.1.le, hz.2.2.le⟩
  change F (C z) = G z
  rw [hCz]
  exact hFG ⟨hzU, hz.2⟩

/-- The stable completion retains the original interface;
its constructed formula is available in the stronger theorem
above for chartwise PL verification. See derivation270. -/
theorem exists_stable_product_completion {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (U K : Set X) (hU : IsOpen U) (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (h : X × ℝ → Y × ℝ) (g : X → Y)
    (hh : IsLocalHomeomorphOn h (univ ×ˢ Ioo (-delta) delta))
    (hg : IsLocalHomeomorphOn g U)
    (hheight : MapsTo h (univ ×ˢ Ioo (-delta) delta) (univ ×ˢ Ioo (-1) 1))
    (hprod : EqOn h (fun z => (g z.1, z.2)) (U ×ˢ Ioo (-delta) delta))
    (w : X → ℝ) (hc : Continuous w) (hw : ∀ x, w x ∈ Icc 0 1)
    (hout : ∀ x, x ∉ U → w x = 0) (hcore : ∀ x ∈ K, w x = 1) :
    ∃ F : X × ℝ → Y × ℝ,
      IsLocalHomeomorphOn F (univ ×ˢ Ioo (-1) 1) ∧
      MapsTo F (univ ×ˢ Ioo (-1) 1) (univ ×ˢ Ioo (-1) 1) ∧
      EqOn F (fun z => (g z.1, z.2)) (K ×ˢ Ioo (-1) 1) := by
  obtain ⟨F, _, hF, himage, hprodF, _⟩ :=
    exists_stable_product_completion_with_formula U K hU delta hd hd1
      h g hh hg hheight hprod w hc hw hout hcore
  exact ⟨F, hF, himage, hprodF⟩

end PLFiberCompression

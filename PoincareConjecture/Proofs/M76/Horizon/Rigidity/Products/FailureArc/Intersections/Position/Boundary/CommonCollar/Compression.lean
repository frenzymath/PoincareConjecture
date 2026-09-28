import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedInverse
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem exists_common_collar_compression
    {E X : Type*} [TopologicalSpace E] [Zero E]
    [TopologicalSpace X] [T2Space X]
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X) (hc : ContinuousOn c (K ×ˢ Icc (0 : ℝ) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (0 : ℝ) r) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ico (0 : ℝ) r))) :
    ∃ D : C(X, X), Function.Injective D ∧
      range D = (c '' (K ×ˢ Ico (0 : ℝ) (r / 2)))ᶜ ∧
      (∀ z ∈ K ×ˢ Icc (0 : ℝ) r, D (c z) = c (z.1, r / 2 + z.2 / 2)) ∧
      ∀ x, x ∉ c '' (K ×ˢ Icc (0 : ℝ) r) → D x = x := by
  classical
  let P := K ×ˢ Icc (0 : ℝ) r
  let A := c '' P
  have hA : IsClosed A := ((hK.prod isCompact_Icc).image_of_continuousOn hc).isClosed
  obtain ⟨k, hk, hleft, hright, hkmap⟩ := hi.exists_inverse_on_image
  have hinj : InjOn c P := by
    intro z hz w hw heq
    exact congrArg Subtype.val (hi.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) heq)
  have hmove {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) :
      r / 2 + s / 2 ∈ Icc (0 : ℝ) r := by
    constructor <;> linarith [hs.1, hs.2]
  let d0 : X → X := fun y => c ((k y).1, r / 2 + (k y).2 / 2)
  have hd0 : ContinuousOn d0 A := by
    apply hc.comp (hk.fst.prodMk (continuousOn_const.add (hk.snd.div_const 2)))
    intro y hy
    exact ⟨(hkmap hy).1, hmove (hkmap hy).2⟩
  have hfix : EqOn d0 id (frontier A) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hA.frontier_subset hy
    have hzr : z.2 = r := by
      by_contra hn
      have hzi : c z ∈ interior A :=
        (ho.subset_interior_iff.mpr (image_mono (prod_mono Subset.rfl Ico_subset_Icc_self)))
          ⟨z, ⟨hz.1, hz.2.1, lt_of_le_of_ne hz.2.2 hn⟩, rfl⟩
      exact hy.2 hzi
    change c ((k (c z)).1, r / 2 + (k (c z)).2 / 2) = c z
    rw [hleft z hz]
    apply congrArg c
    refine Prod.ext rfl ?_
    change r / 2 + z.2 / 2 = z.2
    linarith
  let d : X → X := fun y => if y ∈ A then d0 y else y
  have hd : Continuous d := by
    apply continuous_if
    · exact fun y hy => hfix hy
    · change ContinuousOn d0 (closure A)
      rwa [hA.closure_eq]
    · exact continuous_id.continuousOn
  let D : C(X, X) := ⟨d, hd⟩
  have hvalue (z : E × ℝ) (hz : z ∈ P) :
      D (c z) = c (z.1, r / 2 + z.2 / 2) := by
    change (if c z ∈ A then d0 (c z) else c z) = _
    rw [if_pos (mem_image_of_mem c hz)]
    change c ((k (c z)).1, r / 2 + (k (c z)).2 / 2) = _
    rw [hleft z hz]
  have hout (x : X) (hx : x ∉ A) : D x = x := if_neg hx
  have hDA {x : X} (hx : x ∈ A) : D x ∈ A := by
    obtain ⟨z, hz, rfl⟩ := hx
    rw [hvalue z hz]
    exact mem_image_of_mem c ⟨hz.1, hmove hz.2⟩
  have hDi : Function.Injective D := by
    intro x y hxy
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ A
      · obtain ⟨z, hz, rfl⟩ := hx
        obtain ⟨w, hw, rfl⟩ := hy
        rw [hvalue z hz, hvalue w hw] at hxy
        have heq := hinj (x₁ := (z.1, r / 2 + z.2 / 2))
          (x₂ := (w.1, r / 2 + w.2 / 2)) ⟨hz.1, hmove hz.2⟩ ⟨hw.1, hmove hw.2⟩ hxy
        have hfirst := congrArg Prod.fst heq
        have hlast := congrArg Prod.snd heq
        apply congrArg c
        refine Prod.ext hfirst ?_
        change r / 2 + z.2 / 2 = r / 2 + w.2 / 2 at hlast
        linarith
      · exact False.elim (hy (by rw [← hout y hy, ← hxy]; exact hDA hx))
    · by_cases hy : y ∈ A
      · exact False.elim (hx (by rw [← hout x hx, hxy]; exact hDA hy))
      · simpa only [hout x hx, hout y hy] using hxy
  refine ⟨D, hDi, ?_, hvalue, hout⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩ ⟨w, hw, heq⟩
    have hwP : w ∈ P := ⟨hw.1, hw.2.1, by linarith [hw.2.2]⟩
    by_cases hx : x ∈ A
    · obtain ⟨z, hz, rfl⟩ := hx
      rw [hvalue z hz] at heq
      have he := congrArg Prod.snd
        (hinj (x₂ := (z.1, r / 2 + z.2 / 2)) hwP ⟨hz.1, hmove hz.2⟩ heq)
      change w.2 = r / 2 + z.2 / 2 at he
      linarith [hw.2.2, hz.2.1]
    · rw [hout x hx] at heq
      exact hx ⟨w, hwP, heq⟩
  · intro hy
    by_cases hyA : y ∈ A
    · obtain ⟨z, hz, rfl⟩ := hyA
      have hge : r / 2 ≤ z.2 := by
        by_contra hn
        exact hy ⟨z, ⟨hz.1, hz.2.1, lt_of_not_ge hn⟩, rfl⟩
      have hzP : (z.1, 2 * z.2 - r) ∈ P :=
        ⟨hz.1, by constructor <;> linarith [hz.2.2]⟩
      refine ⟨c (z.1, 2 * z.2 - r), ?_⟩
      rw [hvalue _ hzP]
      apply congrArg c
      refine Prod.ext rfl ?_
      change r / 2 + (2 * z.2 - r) / 2 = z.2
      ring
    · exact ⟨y, hout y hyA⟩

end PoincareConjecture.M76

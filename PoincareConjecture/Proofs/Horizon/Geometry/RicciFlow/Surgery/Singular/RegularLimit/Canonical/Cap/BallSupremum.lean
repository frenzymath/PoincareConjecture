import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal

namespace PoincareConjecture.SingularRegularLimit

theorem continuousAt_sSup_ennreal_sublevel
    {X : Type*} [TopologicalSpace X] (d : X → ℝ≥0∞) (f : X → ℝ)
    (hd : Continuous d) (hf : Continuous f) (x₀ : X) (hx₀ : d x₀ = 0)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hcompact : IsCompact {x | d x ≤ ENNReal.ofReal R})
    (hclosure : {x | d x ≤ ENNReal.ofReal r} ⊆ closure {x | d x < ENNReal.ofReal r}) :
    ContinuousAt (fun s : ℝ => sSup (f '' {x | d x < ENNReal.ofReal s})) r := by
  let K := {x | d x ≤ ENNReal.ofReal R}
  let S := fun s : ℝ => {x | d x < ENNReal.ofReal s}
  have hbdd (s : ℝ) (hs : s ≤ R) : BddAbove (f '' S s) := by
    apply (hcompact.image hf).bddAbove.mono
    apply image_mono
    intro x hx
    exact hx.le.trans (ENNReal.ofReal_le_ofReal hs)
  have hne (s : ℝ) (hs : 0 < s) : (f '' S s).Nonempty := by
    refine ⟨f x₀, ⟨x₀, ?_, rfl⟩⟩
    change d x₀ < ENNReal.ofReal s
    rw [hx₀]
    exact ENNReal.ofReal_pos.mpr hs
  change Tendsto (fun s => sSup (f '' S s)) (𝓝 r) (𝓝 (sSup (f '' S r)))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨_, ⟨x, hx, rfl⟩, hax⟩ := exists_lt_of_lt_csSup (hne r hr) ha
    have hnear : ∀ᶠ s in 𝓝 r, d x < ENNReal.ofReal s :=
      (ENNReal.continuous_ofReal.tendsto r).eventually (Ioi_mem_nhds hx)
    filter_upwards [Ioo_mem_nhds hr hrR, hnear] with s hs hxs
    exact lt_csSup_of_lt (hbdd s hs.2.le) ⟨x, hxs, rfl⟩ hax
  · intro b hb
    obtain ⟨c, hrc, hcb⟩ := exists_between hb
    have hclosed : ∀ x, d x ≤ ENNReal.ofReal r → f x ≤ sSup (f '' S r) := by
      have hbound : closure (S r) ⊆ {x | f x ≤ sSup (f '' S r)} := by
        apply closure_minimal ?_ (isClosed_le hf continuous_const)
        intro x hx
        exact le_csSup (hbdd r hrR.le) ⟨x, hx, rfl⟩
      exact fun x hx => hbound (hclosure hx)
    let B := K ∩ {x | c ≤ f x}
    have hB : IsCompact B := hcompact.inter_right (isClosed_le continuous_const hf)
    have havoid : ∀ᶠ s in 𝓝 r, ∀ x ∈ S s, f x < c := by
      by_cases hBne : B.Nonempty
      · obtain ⟨y, hy, hymin⟩ := hB.exists_isMinOn hBne hd.continuousOn
        have hry : ENNReal.ofReal r < d y := by
          apply lt_of_not_ge
          intro hdy
          exact not_le_of_gt (hrc.trans_le hy.2) (hclosed y hdy)
        have hnear : ∀ᶠ s in 𝓝 r, ENNReal.ofReal s < d y :=
          (ENNReal.continuous_ofReal.tendsto r).eventually (Iio_mem_nhds hry)
        filter_upwards [Ioo_mem_nhds hr hrR, hnear] with s hs hsy
        intro x hx
        apply lt_of_not_ge
        intro hfx
        have hxB : x ∈ B := ⟨hx.le.trans (ENNReal.ofReal_le_ofReal hs.2.le), hfx⟩
        exact (hymin hxB).not_gt (hx.trans hsy)
      · filter_upwards [Ioo_mem_nhds hr hrR] with s hs
        intro x hx
        apply lt_of_not_ge
        intro hfx
        exact hBne ⟨x, hx.le.trans (ENNReal.ofReal_le_ofReal hs.2.le), hfx⟩
    filter_upwards [Ioo_mem_nhds hr hrR, havoid] with s hs hsc
    apply lt_of_le_of_lt (csSup_le (hne s hs.1) ?_) hcb
    rintro _ ⟨x, hx, rfl⟩
    exact (hsc x hx).le

end PoincareConjecture.SingularRegularLimit

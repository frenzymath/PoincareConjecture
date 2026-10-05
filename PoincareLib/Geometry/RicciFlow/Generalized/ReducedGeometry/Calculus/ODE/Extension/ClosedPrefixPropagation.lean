import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Extension.ClosedLeftNeighborhood
import Mathlib.Topology.Order.IntermediateValue

/-!
# Propagation of properties on closed real prefixes

Morgan-Tian Lemma 6.18, pp. 113-114. A supremum argument propagates
a downward-closed prefix property when common local restarts reach
every limiting time and pass every interior time. No closedness of
the set of good prefixes is assumed.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareMT.M14

/-- A relative closed neighborhood has a strict right margin at
every point before the ambient right endpoint, the interior-time
restart condition in Lemma 6.18, pp. 113-114. -/
theorem right_lt_of_Icc_mem_nhdsWithin {a b c d t : ℝ} (hat : a ≤ t) (htb : t < b)
    (hnear : Icc c d ∈ 𝓝[Icc a b] t) : t < d := by
  obtain ⟨N, hN, htN, hsub⟩ := mem_nhdsWithin.mp hnear
  obtain ⟨l, u, ⟨hlt, htu⟩, hln⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hN.mem_nhds htN)
  obtain ⟨q, htq, hq⟩ := exists_between (lt_min htb htu)
  exact htq.trans_le (hsub ⟨hln ⟨hlt.trans htq, hq.trans_le (min_le_right _ _)⟩,
    hat.trans htq.le, hq.le.trans (min_le_left _ _)⟩).2

/-- A downward-closed real prefix property propagates to the final
endpoint if a common restart from any sufficiently nearby earlier
good prefix reaches each limit and passes every interior limit.
This is the closed-endpoint continuation argument of Lemma 6.18,
pp. 113-114. -/
theorem closedPrefix_propagation {a b : ℝ} (P : ℝ → Prop)
    (hmono : ∀ {r s : ℝ}, P r → s ∈ Icc a r → P s)
    (hinit : ∃ r ∈ Ioc a b, P r)
    (hstep : ∀ t ∈ Ioc a b, ∃ c d : ℝ, a ≤ c ∧ c < t ∧ t ≤ d ∧ d ≤ b ∧
      (t < b → t < d) ∧ ∀ r ∈ Ioo c t, P r → P d) : P b := by
  let B := {r | r ∈ Icc a b ∧ P r}
  obtain ⟨r₀, hr₀, hP₀⟩ := hinit
  have hB : B.Nonempty := ⟨r₀, ⟨hr₀.1.le, hr₀.2⟩, hP₀⟩
  have hbound : BddAbove B := ⟨b, fun _ hr => hr.1.2⟩
  let t := sSup B
  have hrt : r₀ ≤ t := le_csSup hbound ⟨⟨hr₀.1.le, hr₀.2⟩, hP₀⟩
  have hat : a < t := hr₀.1.trans_le hrt
  have htb : t ≤ b := csSup_le hB (fun _ hr => hr.1.2)
  obtain ⟨c, d, hac, hct, htd, hdb, hstrict, hrestart⟩ := hstep t ⟨hat, htb⟩
  obtain ⟨m, hcm, hmt⟩ := exists_between hct
  obtain ⟨q, hq, hmq⟩ := exists_lt_of_lt_csSup hB hmt
  have hPd : P d := hrestart m ⟨hcm, hmt⟩
    (hmono hq.2 ⟨hac.trans hcm.le, hmq.le⟩)
  have hdt : d ≤ t := le_csSup hbound ⟨⟨hat.le.trans htd, hdb⟩, hPd⟩
  have hbt : b ≤ t := le_of_not_gt (fun hlt => (hstrict hlt).not_ge hdt)
  have hdb' : d = b := le_antisymm hdb (hbt.trans htd)
  exact hdb' ▸ hPd

end PoincareMT.M14

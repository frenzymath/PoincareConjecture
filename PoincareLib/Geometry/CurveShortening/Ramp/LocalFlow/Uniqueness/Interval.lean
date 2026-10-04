import PoincareLib.Geometry.CurveShortening.Ramp.LocalFlow.C2.Locality
import Mathlib.Topology.Order.IntermediateValue

/-!
# Forward extension of fixed-label uniqueness

One-sided continuous induction extends short-time equality through a
closed interval. Closed uniqueness then gives the exact half-open field
by restriction. MT2007 Claim 19.1, p. 437;
`2026-09-21-uniqueness-graph-comparison-components.md`, sections 3-4.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M63

/-- Forward agreement and closed continuity imply equality through the
final included time. No backward uniqueness or ordinary openness of the
equalizer is assumed. MT2007 Claim 19.1, p. 437; graph comparison
components, section 3. Empty label types are allowed. -/
theorem eqOn_Icc_of_forward_agreement
    {X Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {c d : X → ℝ → Y} {a b : ℝ}
    (hc : ∀ x, ContinuousOn (c x) (Icc a b))
    (hd : ∀ x, ContinuousOn (d x) (Icc a b))
    (hinit : ∀ x, c x a = d x a)
    (hforward : ∀ s ∈ Ico a b, (∀ x, c x s = d x s) →
      ∃ r, s < r ∧ ∀ t ∈ Icc s r, t ≤ b → ∀ x, c x t = d x t) :
    ∀ t ∈ Icc a b, ∀ x, c x t = d x t := by
  let E : Set ℝ := {t | ∀ x, c x t = d x t}
  have hclosed : IsClosed (E ∩ Icc a b) := by
    have hc' : ContinuousOn (fun t x => c x t) (Icc a b) := continuousOn_pi.mpr hc
    have hd' : ContinuousOn (fun t x => d x t) (Icc a b) := continuousOn_pi.mpr hd
    convert isClosed_Icc.isClosed_eq hc' hd' using 1
    ext t
    simp only [E, mem_inter_iff, mem_ofPred_eq, funext_iff]
    exact and_comm
  apply hclosed.Icc_subset_of_forall_mem_nhdsWithin hinit
  intro s hs
  obtain ⟨r, hsr, hagree⟩ := hforward s hs.2 hs.1
  filter_upwards [Ioo_mem_nhdsGT hsr, Ioo_mem_nhdsGT hs.2.2] with t htr htb
  exact hagree t ⟨htr.1.le, htr.2.le⟩ htb.2.le

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)}

/-- The exact closed uniqueness field supplies the frozen half-open
uniqueness field by restriction to strictly shorter closed intervals.
MT2007 Claim 19.1, p. 437; graph comparison components, section 4.
There is no equation or trace assertion at the omitted final endpoint. -/
theorem unique_half_open_of_unique_closed
    (hclosed : ∀ T : ℝ, a < T → T ≤ b → ∀ c d : ℝ → ℝ → M,
      M63C2ShrinkingCurveOn F c (Icc a T) →
      M63C2ShrinkingCurveOn F d (Icc a T) →
      (∀ x, c x a = d x a) → ∀ t ∈ Icc a T, ∀ x, c x t = d x t)
    {T : ℝ} (_haT : a < T) (hTb : T ≤ b)
    {c d : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c (Ico a T))
    (hd : M63C2ShrinkingCurveOn F d (Ico a T))
    (hinit : ∀ x, c x a = d x a) :
    ∀ t ∈ Ico a T, ∀ x, c x t = d x t := by
  intro t ht
  obtain ⟨s, hts, hsT⟩ := exists_between ht.2
  have hsub : Icc a s ⊆ Ico a T := fun _ hy => ⟨hy.1, hy.2.trans_lt hsT⟩
  exact hclosed s (ht.1.trans_lt hts) (hsT.le.trans hTb) c d
    (c2_restrict hc hsub) (c2_restrict hd hsub) hinit t ⟨ht.1, hts.le⟩

end PoincareMT.M63

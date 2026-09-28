import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CirclePhaseIntervals
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set

namespace AddCircle

theorem mapsTo_phase_arc_on_fibers {E : Type*} [TopologicalSpace E]
    (p : ℝ) [Fact (0 < p)] {B : Set E} {a b eta delta : ℝ}
    (heta : 0 < eta) (hdelta : 0 ≤ delta)
    (ha : 0 ≤ a - eta) (hab : a + eta ≤ b - eta) (hb : b + eta ≤ p)
    {f : E × ℝ → AddCircle p} (hc : ContinuousOn f (B ×ˢ Icc (-delta) delta))
    (hf : MapsTo f (B ×ˢ Icc (-delta) delta)
      (openIntervalArc p (a - eta) (a + eta) ∪
        openIntervalArc p (b - eta) (b + eta))) :
    ∀ x ∈ B,
      (f (x, 0) = (a : AddCircle p) →
        MapsTo (fun t => f (x, t)) (Icc (-delta) delta)
          (openIntervalArc p (a - eta) (a + eta))) ∧
      (f (x, 0) = (b : AddCircle p) →
        MapsTo (fun t => f (x, t)) (Icc (-delta) delta)
          (openIntervalArc p (b - eta) (b + eta))) := by
  intro x hx
  let g : ℝ → AddCircle p := fun t => f (x, t)
  have hgc : ContinuousOn g (Icc (-delta) delta) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hx, ht⟩)
  have hpre : IsPreconnected (g '' Icc (-delta) delta) :=
    isPreconnected_Icc.image g hgc
  have hsub : g '' Icc (-delta) delta ⊆
      openIntervalArc p (a - eta) (a + eta) ∪
        openIntervalArc p (b - eta) (b + eta) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hf ⟨hx, ht⟩
  have hdis := disjoint_openIntervalArc_of_le p ha hab hb
  have hzero : (0 : ℝ) ∈ Icc (-delta) delta := ⟨by linarith, hdelta⟩
  constructor
  · intro hphase
    have hbase : g 0 ∈ openIntervalArc p (a - eta) (a + eta) := by
      change f (x, 0) ∈ _
      rw [hphase]
      exact ⟨a, ⟨by linarith, by linarith⟩, rfl⟩
    have hleft := hpre.subset_left_of_subset_union
      (isOpen_openIntervalArc p _ _) (isOpen_openIntervalArc p _ _)
      hdis hsub ⟨g 0, ⟨0, hzero, rfl⟩, hbase⟩
    intro t ht
    exact hleft ⟨t, ht, rfl⟩
  · intro hphase
    have hbase : g 0 ∈ openIntervalArc p (b - eta) (b + eta) := by
      change f (x, 0) ∈ _
      rw [hphase]
      exact ⟨b, ⟨by linarith, by linarith⟩, rfl⟩
    have hright := hpre.subset_right_of_subset_union
      (isOpen_openIntervalArc p _ _) (isOpen_openIntervalArc p _ _)
      hdis hsub ⟨g 0, ⟨0, hzero, rfl⟩, hbase⟩
    intro t ht
    exact hright ⟨t, ht, rfl⟩

theorem exists_real_lift_on_phase_arcs {E : Type*} [TopologicalSpace E]
    (p : ℝ) [Fact (0 < p)] {S : Set E} {a b eta : ℝ}
    (heta : 0 ≤ eta) (ha : 0 ≤ a - eta)
    (hab : a + eta ≤ b - eta) (hb : b + eta ≤ p)
    {f : E → AddCircle p} (hc : ContinuousOn f S)
    (hf : MapsTo f S (openIntervalArc p (a - eta) (a + eta) ∪
      openIntervalArc p (b - eta) (b + eta))) :
    ∃ v : E → ℝ, ContinuousOn v S ∧
      (∀ x ∈ S, (v x : AddCircle p) = f x) ∧
      (∀ x ∈ S, v x ∈ Ioo (0 : ℝ) p) ∧
      (∀ x ∈ S, f x ∈ openIntervalArc p (a - eta) (a + eta) ↔
        v x ∈ Ioo (a - eta) (a + eta)) ∧
      ∀ x ∈ S, f x ∈ openIntervalArc p (b - eta) (b + eta) ↔
        v x ∈ Ioo (b - eta) (b + eta) := by
  let J := openPartialHomeomorphCoe p 0
  have hatop : a + eta ≤ p := by linarith
  have hbbase : 0 ≤ b - eta := by linarith
  have htarget : MapsTo f S J.target := by
    intro x hx
    rcases hf hx with h | h
    · exact openIntervalArc_subset_coe_chart p ha hatop h
    · exact openIntervalArc_subset_coe_chart p hbbase hb h
  let v : E → ℝ := fun x => J.symm (f x)
  have hval (x : E) (hx : x ∈ S) : (v x : AddCircle p) = f x :=
    J.right_inv (htarget hx)
  have hsource (x : E) (hx : x ∈ S) : v x ∈ Ioo (0 : ℝ) p := by
    have h := J.map_target (htarget hx)
    change v x ∈ Ioo (0 : ℝ) (0 + p) at h
    simpa only [zero_add] using h
  refine ⟨v, J.continuousOn_invFun.comp hc htarget, hval, hsource, ?_, ?_⟩
  · intro x hx
    rw [← hval x hx]
    exact coe_mem_openIntervalArc_iff p ha hatop
      ⟨(hsource x hx).1.le, (hsource x hx).2⟩
  · intro x hx
    rw [← hval x hx]
    exact coe_mem_openIntervalArc_iff p hbbase hb
      ⟨(hsource x hx).1.le, (hsource x hx).2⟩

end AddCircle

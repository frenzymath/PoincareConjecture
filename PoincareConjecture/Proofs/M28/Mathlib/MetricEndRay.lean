import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

universe u

namespace PoincareConjecture.M28

structure MetricEndRay {X : Type u} [MetricSpace X]
    (E : UniformSpace.Completion X) (alpha : ℝ) where

  length : ℝ

  length_pos : 0 < length

  length_lt : length < alpha / 4

  point : ℝ → X

  metric : ∀ s ∈ Ioc (0 : ℝ) length, ∀ t ∈ Ioc (0 : ℝ) length,
    dist (point s) (point t) = |s - t|

  radius : ∀ s ∈ Ioc (0 : ℝ) length,
    dist (point s : UniformSpace.Completion X) E = s

namespace MetricEndRay

variable {X : Type u} [MetricSpace X]
  {E : UniformSpace.Completion X} {alpha : ℝ}

def inward (P : MetricEndRay E alpha) (t : ℝ) : X :=
  P.point (P.length - t)

theorem inward_metric (P : MetricEndRay E alpha)
    (s : ℝ) (hs : s ∈ Ico (0 : ℝ) P.length)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) P.length) :
    dist (P.inward s) (P.inward t) = |s - t| := by
  unfold inward
  rw [P.metric _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
    _ ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    show P.length - s - (P.length - t) = -(s - t) by ring, abs_neg]

theorem inward_radius (P : MetricEndRay E alpha)
    (s : ℝ) (hs : s ∈ Ico (0 : ℝ) P.length) :
    dist (P.inward s : UniformSpace.Completion X) E = P.length - s :=
  P.radius _ ⟨by linarith [hs.2], by linarith [hs.1]⟩

theorem continuousOn_point (P : MetricEndRay E alpha) :
    ContinuousOn P.point (Ioc (0 : ℝ) P.length) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hi : Isometry (fun s : Ioc (0 : ℝ) P.length => P.point s.1) := by
    apply Isometry.of_dist_eq
    intro s t
    simpa only [Subtype.dist_eq, Real.dist_eq] using P.metric s.1 s.2 t.1 t.2
  exact hi.continuous

theorem completion_triangle (P Q : MetricEndRay E alpha)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) P.length)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) Q.length) :
    |s - t| ≤ dist (P.point s) (Q.point t) ∧
      dist (P.point s) (Q.point t) ≤ s + t := by
  constructor
  · simpa only [UniformSpace.Completion.dist_eq, P.radius s hs, Q.radius t ht] using
      abs_dist_sub_le (P.point s : UniformSpace.Completion X)
        (Q.point t : UniformSpace.Completion X) E
  · simpa only [UniformSpace.Completion.dist_eq, P.radius s hs, Q.radius t ht] using
      dist_triangle_right (P.point s : UniformSpace.Completion X)
        (Q.point t : UniformSpace.Completion X) E

def ofInward {a : ℝ} (ha : 0 < a) (hsmall : a < alpha / 4)
    (gamma : ℝ → X)
    (hmetric : ∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
      dist (gamma s) (gamma t) = |s - t|)
    (hradius : ∀ s ∈ Ico (0 : ℝ) a,
      dist (gamma s : UniformSpace.Completion X) E = a - s) :
    MetricEndRay E alpha where
  length := a
  length_pos := ha
  length_lt := hsmall
  point := fun s => gamma (a - s)
  metric := by
    intro s hs t ht
    rw [hmetric _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
      _ ⟨by linarith [ht.2], by linarith [ht.1]⟩,
      show a - s - (a - t) = -(s - t) by ring, abs_neg]
  radius := by
    intro s hs
    rw [hradius _ ⟨by linarith [hs.2], by linarith [hs.1]⟩]
    ring

theorem ofInward_endpoint {a : ℝ} (ha : 0 < a) (hsmall : a < alpha / 4)
    (gamma : ℝ → X)
    (hmetric : ∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
      dist (gamma s) (gamma t) = |s - t|)
    (hradius : ∀ s ∈ Ico (0 : ℝ) a,
      dist (gamma s : UniformSpace.Completion X) E = a - s) :
    (ofInward ha hsmall gamma hmetric hradius).point a = gamma 0 := by
  simp only [ofInward, sub_self]

def SameEndGerm (P Q : MetricEndRay E alpha) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c ≤ P.length ∧ c ≤ Q.length ∧
    Set.EqOn P.point Q.point (Ioc (0 : ℝ) c)

end MetricEndRay
end PoincareConjecture.M28

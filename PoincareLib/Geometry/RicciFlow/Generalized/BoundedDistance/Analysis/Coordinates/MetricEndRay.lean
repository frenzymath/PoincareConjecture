import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite outward metric rays toward a missing completion point

Only the positive tested domain is constrained. These data retain the
actual source points and the exact completion radius, so no smoothness,
germ equivalence or angular limit is part of the definition.
Source: Morgan--Tian Lemmas 10.16 and 10.21, pp. 258-259;
M28 derivations 135, 151 and 152b.
-/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

universe u

namespace PoincareMT.M28

/-- A finite outward ray whose parameter is its distance from one
completion point. Values outside `(0, length]` are not constrained.
The common length cap is the retained fixed-sphere barrier.
Source: MT Lemma 10.21, p. 259; derivation 152b. -/
structure MetricEndRay {X : Type u} [MetricSpace X]
    (E : UniformSpace.Completion X) (alpha : ℝ) where
  /-- The finite positive outer radius. -/
  length : ℝ
  /-- The outer radius is positive. -/
  length_pos : 0 < length
  /-- Every tested point is inside the same comparison barrier. -/
  length_lt : length < alpha / 4
  /-- The actual source point map, arbitrarily totalized outside its domain. -/
  point : ℝ → X
  /-- Exact unit-speed distances on the tested interval. -/
  metric : ∀ s ∈ Ioc (0 : ℝ) length, ∀ t ∈ Ioc (0 : ℝ) length,
    dist (point s) (point t) = |s - t|
  /-- The radial parameter is the actual completion distance. -/
  radius : ∀ s ∈ Ioc (0 : ℝ) length,
    dist (point s : UniformSpace.Completion X) E = s

namespace MetricEndRay

variable {X : Type u} [MetricSpace X]
  {E : UniformSpace.Completion X} {alpha : ℝ}

/-- Reverse an outward ray on its finite inward interval.
Source: MT Lemma 10.21, p. 259; derivation 152b. -/
def inward (P : MetricEndRay E alpha) (t : ℝ) : X :=
  P.point (P.length - t)

/-- The inward reparametrization has exactly the distance hypothesis
of the proved missing-end comparison. Source: derivations 151/152b. -/
theorem inward_metric (P : MetricEndRay E alpha)
    (s : ℝ) (hs : s ∈ Ico (0 : ℝ) P.length)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) P.length) :
    dist (P.inward s) (P.inward t) = |s - t| := by
  unfold inward
  rw [P.metric _ ⟨by linarith [hs.2], by linarith [hs.1]⟩
    _ ⟨by linarith [ht.2], by linarith [ht.1]⟩,
    show P.length - s - (P.length - t) = -(s - t) by ring, abs_neg]

/-- The inward radius is the remaining interval length.
Source: MT Lemma 10.16, p. 258; derivation 152b. -/
theorem inward_radius (P : MetricEndRay E alpha)
    (s : ℝ) (hs : s ∈ Ico (0 : ℝ) P.length) :
    dist (P.inward s : UniformSpace.Completion X) E = P.length - s :=
  P.radius _ ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- Exact source distances make the tested outward map continuous,
including its outer endpoint. Source: derivations 135 and 152b. -/
theorem continuousOn_point (P : MetricEndRay E alpha) :
    ContinuousOn P.point (Ioc (0 : ℝ) P.length) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hi : Isometry (fun s : Ioc (0 : ℝ) P.length => P.point s.1) := by
    apply Isometry.of_dist_eq
    intro s t
    simpa only [Subtype.dist_eq, Real.dist_eq] using P.metric s.1 s.2 t.1 t.2
  exact hi.continuous

/-- Both completion triangle bounds use the literal source metric.
Source: MT Lemma 10.21, p. 259; derivation 152b. -/
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

/-- Actual inward rays from the compact-prefix producer give outward
data without changing any points or the completion metric.
Source: MT Lemma 10.16, p. 258; derivations 135 and 152b. -/
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

/-- The outer endpoint of the reversed datum is literally the inward
ray's original basepoint. Source: derivations 135 and 152b. -/
theorem ofInward_endpoint {a : ℝ} (ha : 0 < a) (hsmall : a < alpha / 4)
    (gamma : ℝ → X)
    (hmetric : ∀ s ∈ Ico (0 : ℝ) a, ∀ t ∈ Ico (0 : ℝ) a,
      dist (gamma s) (gamma t) = |s - t|)
    (hradius : ∀ s ∈ Ico (0 : ℝ) a,
      dist (gamma s : UniformSpace.Completion X) E = a - s) :
    (ofInward ha hsmall gamma hmetric hradius).point a = gamma 0 := by
  simp only [ofInward, sub_self]

/-- Equality of actual points on one common positive radial interval.
The definition disregards both totalizations outside their domains.
Source: MT Lemma 10.22, pp. 259-260; derivation 152b. -/
def SameEndGerm (P Q : MetricEndRay E alpha) : Prop :=
  ∃ c : ℝ, 0 < c ∧ c ≤ P.length ∧ c ≤ Q.length ∧
    Set.EqOn P.point Q.point (Ioc (0 : ℝ) c)

end MetricEndRay
end PoincareMT.M28

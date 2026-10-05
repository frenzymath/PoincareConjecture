import PoincareLib.Topology.Manifold.Smoothing.Dehn.Arcs.Mathlib.PrescribedTwoIntervalCircle

/-!
# Comparing actual target paths through one marked source interval

Two source paths with the same endpoints inside the constructed complementary
interval give endpoint-relative homotopic paths in the target mark. Only
continuity on that interval is used. See Dehn039, sections 5--7.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.Dehn

/-- Compare two literal target paths by their actual lifts to the same source
interval. No homotopy or target simple-connectedness hypothesis is needed. -/
theorem marked_interval_paths_homotopic
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {B : Set E} {Z : Set X} (c : Icc (0 : ℝ) 1 ≃ₜ B)
    (f : E → X) (hf : ContinuousOn f B) (hfZ : MapsTo f B Z)
    {a b : E} (p q : Path a b)
    (hp : ∀ t, p t ∈ B) (hq : ∀ t, q t ∈ B)
    {x y : Z} (P Q : Path x y)
    (hP : ∀ t, (P t : X) = f (p t)) (hQ : ∀ t, (Q t : X) = f (q t)) :
    P.Homotopic Q := by
  have ha : a ∈ B := by simpa only [Path.source] using hp 0
  have hb : b ∈ B := by simpa only [Path.target] using hp 1
  let pB : Path (⟨a, ha⟩ : B) ⟨b, hb⟩ :=
    { toFun := fun t ↦ ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let qB : Path (⟨a, ha⟩ : B) ⟨b, hb⟩ :=
    { toFun := fun t ↦ ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  let F : C(B, Z) :=
    ⟨fun z ↦ ⟨f z, hfZ z.property⟩, hf.domRestrict.subtype_mk _⟩
  have hx : x = F ⟨a, ha⟩ := by
    apply Subtype.ext
    change (x : X) = f a
    simpa only [Path.source] using hP 0
  have hy : y = F ⟨b, hb⟩ := by
    apply Subtype.ext
    change (y : X) = f b
    simpa only [Path.target] using hP 1
  have h := ((homotopic_of_interval_chart c pB qB).map F).pathCast hx hy
  have hPeq : (pB.map F.continuous).cast hx hy = P := by
    apply Path.ext
    funext t
    apply Subtype.ext
    exact (hP t).symm
  have hQeq : (qB.map F.continuous).cast hx hy = Q := by
    apply Path.ext
    funext t
    apply Subtype.ext
    exact (hQ t).symm
  simpa only [hPeq, hQeq] using h

end PoincareMT.M76.Dehn

import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder F C origin scale I U)

private noncomputable def clockForward (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) : C.carrier → (F.slice t).carrier := by
  subst t
  exact e.forward s hs

private noncomputable def clockInverse (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) : (F.slice t).carrier → C.carrier := by
  subst t
  exact e.inverse s hs

private theorem clockForward_smooth (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (clockForward e s hs t h) U := by
  subst t
  exact e.forward_smooth s hs

private theorem clockInverse_smooth (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (clockInverse e s hs t h)
      (clockForward e s hs t h '' U) := by
  subst t
  exact e.inverse_smooth s hs

private theorem clock_left_inverse (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) :
    LeftInvOn (clockInverse e s hs t h) (clockForward e s hs t h) U := by
  subst t
  exact e.left_inverse s hs

private theorem clock_right_inverse (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) :
    LeftInvOn (clockForward e s hs t h) (clockInverse e s hs t h)
      (clockForward e s hs t h '' U) := by
  subst t
  exact e.right_inverse s hs

private theorem clockForward_point (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) (x : C.carrier) :
    (⟨t, clockForward e s hs t h x⟩ : F.point) = e.pointMap s hs x := by
  subst t
  rfl

private theorem clockForward_inner (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) (x : C.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (F.metric t).inner (clockForward e s hs t h x)
      (mfderiv (𝓡 3) (𝓡 3) (clockForward e s hs t h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (clockForward e s hs t h) x w) =
    (F.metric (origin + s / scale)).inner (e.forward s hs x)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x w) := by
  subst t
  rfl

private theorem clockForward_vertical (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) (x : C.carrier)
    (b : F.box_index) (y : (F.box b).carrier.carrier)
    (hb : origin + s / scale ∈ (F.box b).interval)
    (he : e.forward s hs x = (F.box b).forward (origin + s / scale) hb y) :
    ∃ ht : t ∈ (F.box b).interval,
      clockForward e s hs t h x = (F.box b).forward t ht y := by
  subst t
  exact ⟨hb, he⟩

variable (a : ℝ) {J : Set ℝ} (hrange : MapsTo (fun s => a + scale * s) J I)

include e in
private theorem physicalClock (s : ℝ) :
    (origin + a / scale) + s / 1 = origin + (a + scale * s) / scale := by
  rw [div_one, add_div, mul_div_cancel_left₀ _ e.scale_pos.ne']
  ring

noncomputable def limitNoncollapseCylinderReclock :
    GeneralizedFlowCylinder F C (origin + a / scale) 1 J U := by
  refine {
    scale_pos := by norm_num
    forward := fun s hs => clockForward e (a + scale * s) (hrange hs) _
      (physicalClock e a s)
    inverse := fun s hs => clockInverse e (a + scale * s) (hrange hs) _
      (physicalClock e a s)
    forward_smooth := fun s hs => clockForward_smooth e _ (hrange hs) _
      (physicalClock e a s)
    inverse_smooth := fun s hs => clockInverse_smooth e _ (hrange hs) _
      (physicalClock e a s)
    left_inverse := fun s hs => clock_left_inverse e _ (hrange hs) _
      (physicalClock e a s)
    right_inverse := fun s hs => clock_right_inverse e _ (hrange hs) _
      (physicalClock e a s)
    embedding := ?_
    vertical_compatibility := ?_
  }
  · have hphi : Topology.IsEmbedding (fun s : ℝ => a + scale * s) :=
      (Homeomorph.addLeft a).isEmbedding.comp
        (Homeomorph.mulLeft₀ scale e.scale_pos.ne').isEmbedding
    have h := e.embedding.comp ((hphi.restrict hrange).prodMap Topology.IsEmbedding.id)
    have heq :
        (fun p : J × U =>
          (⟨(origin + a / scale) + p.1.1 / 1,
            clockForward e (a + scale * p.1.1) (hrange p.1.2) _
              (physicalClock e a p.1.1) p.2.1⟩ : F.point)) =
        (fun p : J × U => e.pointMap (a + scale * p.1.1) (hrange p.1.2) p.2.1) := by
      funext p
      exact clockForward_point e _ _ _ _ _
    rw [heq]
    exact h
  · intro s hs x hx
    obtain ⟨b, y, δ, hδ, h⟩ := e.vertical_compatibility _ (hrange hs) x hx
    refine ⟨b, y, δ / scale, div_pos hδ e.scale_pos, ?_⟩
    intro s' hs' hnear
    have hnear' : |(a + scale * s') - (a + scale * s)| < δ := by
      rw [show (a + scale * s') - (a + scale * s) = scale * (s' - s) by ring,
        abs_mul, abs_of_pos e.scale_pos]
      have hbound := (lt_div_iff₀ e.scale_pos).mp hnear
      nlinarith
    obtain ⟨hb, he⟩ := h _ (hrange hs') hnear'
    exact clockForward_vertical e _ _ _ (physicalClock e a s') x b y hb he

theorem limitNoncollapseCylinderReclock_pointMap (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) :
    (limitNoncollapseCylinderReclock e a hrange).pointMap s hs x =
      e.pointMap (a + scale * s) (hrange hs) x :=
  clockForward_point e _ _ _ (physicalClock e a s) _

theorem limitNoncollapseCylinderReclock_pullbackInner (s : ℝ) (hs : s ∈ J)
    (x : C.carrier) (v w : TangentSpace (𝓡 3) x) :
    (limitNoncollapseCylinderReclock e a hrange).pullbackInner s hs x v w =
      e.pullbackInner (a + scale * s) (hrange hs) x v w / scale := by
  change 1 * (F.metric _).inner
      (clockForward e _ _ _ (physicalClock e a s) x)
      (mfderiv (𝓡 3) (𝓡 3) (clockForward e _ _ _ (physicalClock e a s)) x v)
      (mfderiv (𝓡 3) (𝓡 3) (clockForward e _ _ _ (physicalClock e a s)) x w) = _
  rw [one_mul, clockForward_inner]
  simp only [GeneralizedFlowCylinder.pullbackInner,
    mul_div_cancel_left₀ _ e.scale_pos.ne']

end PoincareConjecture.M47

import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Generalized.Cylinder
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.GroupWithZero

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

noncomputable section

namespace PoincareConjecture.GeneralizedRicciFlowData

def sliceDiffeomorphOfTimeEq (F : GeneralizedRicciFlowData.{u}) {s t : ℝ} (h : s = t) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice s).carrier (F.slice t).carrier ∞ := by
  subst t
  exact Diffeomorph.refl (𝓡 3) (F.slice s).carrier ∞

theorem sliceDiffeomorphOfTimeEq_point (F : GeneralizedRicciFlowData.{u})
    {s t : ℝ} (h : s = t) (x : (F.slice s).carrier) :
    (⟨t, F.sliceDiffeomorphOfTimeEq h x⟩ : F.point) = ⟨s, x⟩ := by
  subst t
  rfl

theorem sliceDiffeomorphOfTimeEq_metric (F : GeneralizedRicciFlowData.{u})
    {s t : ℝ} (h : s = t) (x : (F.slice s).carrier)
    (v w : TangentSpace (𝓡 3) x) :
    (F.metric t).inner (F.sliceDiffeomorphOfTimeEq h x)
      (mfderiv (𝓡 3) (𝓡 3) (F.sliceDiffeomorphOfTimeEq h) x v)
      (mfderiv (𝓡 3) (𝓡 3) (F.sliceDiffeomorphOfTimeEq h) x w) =
      (F.metric s).inner x v w := by
  subst t
  change (F.metric s).inner x (mfderiv (𝓡 3) (𝓡 3) id x v)
    (mfderiv (𝓡 3) (𝓡 3) id x w) = _
  rw [mfderiv_id]
  rfl

end PoincareConjecture.GeneralizedRicciFlowData

namespace PoincareConjecture.GeneralizedFlowCylinder

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : GeneralizedFlowCylinder F C a q I U)

include e in
theorem physical_clock_eq (t : ℝ) : a + ((t - a) * q) / q = t := by
  rw [mul_div_cancel_right₀ _ e.scale_pos.ne']
  ring

def forwardAtTime (t : ℝ) (ht : (t - a) * q ∈ I) : C.carrier → (F.slice t).carrier :=
  F.sliceDiffeomorphOfTimeEq (e.physical_clock_eq t) ∘ e.forward ((t - a) * q) ht

def inverseAtTime (t : ℝ) (ht : (t - a) * q ∈ I) : (F.slice t).carrier → C.carrier :=
  e.inverse ((t - a) * q) ht ∘ (F.sliceDiffeomorphOfTimeEq (e.physical_clock_eq t)).symm

theorem forwardAtTime_point (t : ℝ) (ht : (t - a) * q ∈ I) (x : C.carrier) :
    (⟨t, e.forwardAtTime t ht x⟩ : F.point) = e.pointMap ((t - a) * q) ht x :=
  F.sliceDiffeomorphOfTimeEq_point (e.physical_clock_eq t) _

theorem forwardAtTime_smooth (t : ℝ) (ht : (t - a) * q ∈ I) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.forwardAtTime t ht) U :=
  (F.sliceDiffeomorphOfTimeEq (e.physical_clock_eq t)).contMDiff.comp_contMDiffOn
    (e.forward_smooth _ ht)

theorem inverseAtTime_smooth (t : ℝ) (ht : (t - a) * q ∈ I) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.inverseAtTime t ht) (e.forwardAtTime t ht '' U) := by
  apply (e.inverse_smooth _ ht).comp
    (F.sliceDiffeomorphOfTimeEq (e.physical_clock_eq t)).symm.contMDiff.contMDiffOn
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, hx, by simp [forwardAtTime]⟩

theorem inverseAtTime_forwardAtTime (t : ℝ) (ht : (t - a) * q ∈ I)
    {x : C.carrier} (hx : x ∈ U) :
    e.inverseAtTime t ht (e.forwardAtTime t ht x) = x := by
  simp only [inverseAtTime, forwardAtTime, Function.comp_apply,
    Diffeomorph.symm_apply_apply, e.left_inverse _ ht hx]

theorem forwardAtTime_inverseAtTime (t : ℝ) (ht : (t - a) * q ∈ I)
    {y : (F.slice t).carrier} (hy : y ∈ e.forwardAtTime t ht '' U) :
    e.forwardAtTime t ht (e.inverseAtTime t ht y) = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [e.inverseAtTime_forwardAtTime t ht hx]

theorem forwardAtTime_embedding :
    Topology.IsEmbedding (fun p : {t : ℝ | (t - a) * q ∈ I} × U =>
      (⟨p.1, e.forwardAtTime p.1 p.1.property p.2⟩ : F.point)) := by
  let clock : ℝ ≃ₜ ℝ := (Homeomorph.addRight (-a)).trans
    (Homeomorph.mulRight₀ q e.scale_pos.ne')
  have hclock : MapsTo clock {t : ℝ | (t - a) * q ∈ I} I := by
    intro t ht
    simpa only [clock, Homeomorph.trans_apply, Homeomorph.coe_addRight,
      Homeomorph.coe_mulRight₀, sub_eq_add_neg, mem_ofPred_eq] using ht
  have heq : (fun p : {t : ℝ | (t - a) * q ∈ I} × U =>
      (⟨p.1, e.forwardAtTime p.1 p.1.property p.2⟩ : F.point)) =
      (fun p : I × U => e.pointMap p.1 p.1.property p.2) ∘
        Prod.map hclock.restrict id := by
    funext p
    exact e.forwardAtTime_point _ _ _
  rw [heq]
  exact e.embedding.comp ((clock.isEmbedding.restrict hclock).prodMap Topology.IsEmbedding.id)

theorem forwardAtTime_vertical_compatibility (t : ℝ) (ht : (t - a) * q ∈ I)
    (x : C.carrier) (hx : x ∈ U) :
    ∃ b, ∃ y : (F.box b).carrier.carrier, ∃ δ : ℝ, 0 < δ ∧
      ∀ s hs, |s - t| < δ → ∃ hb : s ∈ (F.box b).interval,
        e.forwardAtTime s hs x = (F.box b).forward s hb y := by
  obtain ⟨b, y, δ, hδ, hloc⟩ := e.vertical_compatibility ((t - a) * q) ht x hx
  refine ⟨b, y, δ / q, div_pos hδ e.scale_pos, ?_⟩
  intro s hs hst
  have hdist : |(s - a) * q - (t - a) * q| < δ := by
    rw [show (s - a) * q - (t - a) * q = (s - t) * q by ring,
      abs_mul, abs_of_pos e.scale_pos]
    exact (lt_div_iff₀ e.scale_pos).mp hst
  obtain ⟨hb, heq⟩ := hloc ((s - a) * q) hs hdist
  have hb' : s ∈ (F.box b).interval := e.physical_clock_eq s ▸ hb
  refine ⟨hb', ?_⟩
  have hpoint := e.forwardAtTime_point s hs x
  change (⟨s, e.forwardAtTime s hs x⟩ : F.point) =
    ⟨a + ((s - a) * q) / q, e.forward ((s - a) * q) hs x⟩ at hpoint
  rw [heq] at hpoint
  have hbox (v w : ℝ) (hv : v ∈ (F.box b).interval) (hw : w ∈ (F.box b).interval)
      (hvw : v = w) : (⟨v, (F.box b).forward v hv y⟩ : F.point) =
      ⟨w, (F.box b).forward w hw y⟩ := by
    subst w
    rfl
  exact eq_of_heq (Sigma.mk.inj_iff.mp
    (hpoint.trans (hbox _ s hb hb' (e.physical_clock_eq s)))).2

end PoincareConjecture.GeneralizedFlowCylinder

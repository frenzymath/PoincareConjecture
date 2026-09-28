import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRetainedTensor
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialJoining

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

theorem exists_source_initial_birth_slice_chart
    {F : SurgeryFlowData.{u}} {T q : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    {I : Set ℝ} {V : Set (F.event T hT).terminal.carrier}
    (e : SurgeryFlowCylinder F (F.event T hT).terminal T q I V)
    (hV : IsOpen V) (hzero : (0 : ℝ) ∈ I)
    (hnegative : V ⊆ ((F.event T hT).necks i).neck.region
      (-((F.event T hT).necks i).neck.epsilon⁻¹) 0)
    (hmap : ∀ x, HEq (e.forward 0 hzero x)
      ((F.event T hT).retention.map ((F.event T hT).limit_identify.inverse x))) :
    ∃ D : PartialDiffeomorph (𝓡 3) (𝓡 3)
        (F.event T hT).terminal.carrier (F.slice T).carrier ∞,
      D.source = V ∧
      (∀ x, HEq (D x) (e.forward 0 hzero x)) ∧
      (∀ x, D x = (F.event T hT).retention.map ((F.event T hT).limit_identify.inverse x)) ∧
      ∀ x ∈ V, ∀ v w : TangentSpace (𝓡 3) x,
        (F.metric T).inner (D x)
          (mfderiv (𝓡 3) (𝓡 3) D x v) (mfderiv (𝓡 3) (𝓡 3) D x w) =
            (F.event T hT).limit_metric.inner x v w := by
  let chart := M44.cylinderSliceChart e hV 0 hzero
  let castChart (t : ℝ) (ht : T + 0 / q = t) :
      PartialDiffeomorph (𝓡 3) (𝓡 3)
        (F.event T hT).terminal.carrier (F.slice t).carrier ∞ :=
    Eq.ndrec (motive := fun r => PartialDiffeomorph (𝓡 3) (𝓡 3)
      (F.event T hT).terminal.carrier (F.slice r).carrier ∞) chart ht
  have hsource (t : ℝ) (ht : T + 0 / q = t) : (castChart t ht).source = V := by
    cases ht
    rfl
  have hpoint (t : ℝ) (ht : T + 0 / q = t) (x : (F.event T hT).terminal.carrier) :
      HEq (castChart t ht x) (e.forward 0 hzero x) := by
    cases ht
    rfl
  let D := castChart T (by simp only [zero_div, add_zero])
  have hD (x : (F.event T hT).terminal.carrier) :
      D x = (F.event T hT).retention.map ((F.event T hT).limit_identify.inverse x) :=
    eq_of_heq ((hpoint T _ x).trans (hmap x))
  refine ⟨D, hsource T _, hpoint T _, hD, ?_⟩
  intro x hx v w
  have hfun : (D : (F.event T hT).terminal.carrier → (F.slice T).carrier) =
      (F.event T hT).retention.map ∘ (F.event T hT).limit_identify.inverse := funext hD
  rw [hfun]
  exact source_initial_retained_limit_metric hT i (hnegative hx) v w

theorem source_initial_birth_slice_capture
    {F : SurgeryFlowData.{u}} {T A : ℝ} (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] (i : Fin (F.event T hT).cap_count)
    (initial : SurgeryCapInitialComparison F T hT i A)
    {U : Set StandardCapSpace} (hU : IsOpen U)
    (hsource : U ⊆ F.standard_initial.metric.ball 0 A)
    (havoid : ∀ x ∈ U, initial.chart x ∉ ((F.event T hT).caps i).carrier)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3)
      (F.event T hT).terminal.carrier (F.slice T).carrier ∞)
    (hD : ∀ x, D x = (F.event T hT).retention.map
      ((F.event T hT).limit_identify.inverse x))
    (hcapture : MapsTo (sourceInitialOldMap initial) U D.source) :
    IsOpen (initial.chart '' U) ∧ initial.chart '' U ⊆ D.target ∧
      ∀ x ∈ U, D (sourceInitialOldMap initial x) = initial.chart x ∧
        D.symm (initial.chart x) = sourceInitialOldMap initial x := by
  have hopen : IsOpen (initial.chart '' U) :=
    Poincare.isOpen_image_of_smooth_leftInvOn hU
      (initial.chart_smooth.mono hsource)
      (initial.inverse_smooth.mono (image_subset_range _ _))
      (initial.left_inverse.mono hsource)
  have hpoint (x : StandardCapSpace) (hx : x ∈ U) :
      D (sourceInitialOldMap initial x) = initial.chart x := by
    have hr := source_initial_chart_retention hT i initial (hsource hx) (havoid x hx)
    have hreg := (F.event T hT).retained_pre_subset (interior_subset hr.2.1)
    rw [hD, sourceInitialOldMap, (F.event T hT).limit_identify.left_inverse hreg,
      (F.event T hT).retention.right_inverse (interior_subset hr.1)]
  refine ⟨hopen, ?_, fun x hx => ⟨hpoint x hx, ?_⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← hpoint x hx]
    exact D.map_source (hcapture hx)
  · rw [← hpoint x hx]
    exact D.left_inv (hcapture hx)

end PoincareConjecture.M47

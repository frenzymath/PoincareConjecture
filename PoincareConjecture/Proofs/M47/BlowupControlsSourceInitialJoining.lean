import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialRetention











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47

variable {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
  [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}


def sourceInitialOldMap (initial : SurgeryCapInitialComparison F t hT i A) :
    StandardCapSpace → (F.event t hT).terminal.carrier :=
  fun x => (F.event t hT).limit_identify.map
    ((F.event t hT).retention.inverse (initial.chart x))



theorem source_initial_old_map_properties
    (initial : SurgeryCapInitialComparison F t hT i A) {U : Set StandardCapSpace}
    (hsource : U ⊆ F.standard_initial.metric.ball 0 A)
    (havoid : ∀ x ∈ U, initial.chart x ∉ ((F.event t hT).caps i).carrier) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (sourceInitialOldMap initial) U ∧
      InjOn (sourceInitialOldMap initial) U ∧
      MapsTo (sourceInitialOldMap initial) U
        (((F.event t hT).necks i).neck.region
          (-((F.event t hT).necks i).neck.epsilon⁻¹) 0) := by
  let E := F.event t hT
  let p := E.retention.inverse ∘ initial.chart
  have hret (x : StandardCapSpace) (hx : x ∈ U) :=
    source_initial_chart_retention hT i initial (hsource hx) (havoid x hx)
  have hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p U :=
    E.retention.inverse_smooth.comp (initial.chart_smooth.mono hsource)
      (fun x hx => show initial.chart x ∈ E.retained_post from
        interior_subset (hret x hx).1)
  have hreg (x : StandardCapSpace) (hx : x ∈ U) : p x ∈ E.regular_limit :=
    E.retained_pre_subset (interior_subset (hret x hx).2.1)
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (sourceInitialOldMap initial) U :=
    E.limit_identify.map_smooth.comp hp (fun x hx => hreg x hx)
  refine ⟨hf, ?_, fun x hx => (hret x hx).2.2⟩
  intro x hx y hy hxy
  have hpEq : p x = p y := by
    calc
      p x = E.limit_identify.inverse (E.limit_identify.map (p x)) :=
        (E.limit_identify.left_inverse (hreg x hx)).symm
      _ = E.limit_identify.inverse (E.limit_identify.map (p y)) :=
        congrArg E.limit_identify.inverse hxy
      _ = p y := E.limit_identify.left_inverse (hreg y hy)
  have hchart := congrArg E.retention.map hpEq
  change E.retention.map (E.retention.inverse (initial.chart x)) =
    E.retention.map (E.retention.inverse (initial.chart y)) at hchart
  rw [E.retention.right_inverse (interior_subset (hret x hx).1),
    E.retention.right_inverse (interior_subset (hret y hy).1)] at hchart
  have hinv := congrArg initial.inverse hchart
  rwa [initial.left_inverse (hsource hx), initial.left_inverse (hsource hy)] at hinv



theorem source_initial_old_map_metric
    (initial : SurgeryCapInitialComparison F t hT i A) {U : Set StandardCapSpace}
    (hU : IsOpen U) (hsource : U ⊆ F.standard_initial.metric.ball 0 A)
    (havoid : ∀ x ∈ U, initial.chart x ∉ ((F.event t hT).caps i).carrier)
    {x : StandardCapSpace} (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (F.event t hT).limit_metric.inner (sourceInitialOldMap initial x)
      (mfderiv (𝓡 3) (𝓡 3) (sourceInitialOldMap initial) x v)
      (mfderiv (𝓡 3) (𝓡 3) (sourceInitialOldMap initial) x w) =
      (F.metric t).inner (initial.chart x)
        (mfderiv (𝓡 3) (𝓡 3) initial.chart x v)
        (mfderiv (𝓡 3) (𝓡 3) initial.chart x w) := by
  let E := F.event t hT
  let p := E.retention.inverse ∘ initial.chart
  have hret (y : StandardCapSpace) (hy : y ∈ U) :=
    source_initial_chart_retention hT i initial (hsource hy) (havoid y hy)
  have hp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ p U :=
    E.retention.inverse_smooth.comp (initial.chart_smooth.mono hsource)
      (fun y hy => show initial.chart y ∈ E.retained_post from
        interior_subset (hret y hy).1)
  have hpx : p x ∈ interior E.retained_pre := (hret x hx).2.1
  have hreg : p x ∈ E.regular_limit := E.retained_pre_subset (interior_subset hpx)
  have hpAt := ((hp x hx).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hrAt := ((E.retention.map_smooth.mono interior_subset _ hpx).contMDiffAt
    (isOpen_interior.mem_nhds hpx)).mdifferentiableAt (by simp)
  have hlAt := ((E.limit_identify.map_smooth _ hreg).contMDiffAt
    (E.regular_limit_open.mem_nhds hreg)).mdifferentiableAt (by simp)
  have heq : E.retention.map ∘ p =ᶠ[𝓝 x] initial.chart := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact E.retention.right_inverse (interior_subset (hret y hy).1)
  have hdR : mfderiv (𝓡 3) (𝓡 3) initial.chart x =
      (mfderiv (𝓡 3) (𝓡 3) E.retention.map (p x)).comp
        (mfderiv (𝓡 3) (𝓡 3) p x) :=
    heq.mfderiv_eq.symm.trans (mfderiv_comp x hrAt hpAt)
  have hdF : mfderiv (𝓡 3) (𝓡 3) (sourceInitialOldMap initial) x =
      (mfderiv (𝓡 3) (𝓡 3) E.limit_identify.map (p x)).comp
        (mfderiv (𝓡 3) (𝓡 3) p x) := mfderiv_comp x hlAt hpAt
  have hmetric := E.retained_metric (p x) (interior_subset hpx)
    (mfderiv (𝓡 3) (𝓡 3) p x v) (mfderiv (𝓡 3) (𝓡 3) p x w)
  have hpoint : E.retention.map (p x) = initial.chart x := heq.self_of_nhds
  rw [hpoint] at hmetric
  rw [hdF, hdR]
  exact hmetric.symm

end PoincareConjecture.M47

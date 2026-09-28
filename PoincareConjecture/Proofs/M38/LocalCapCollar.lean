import PoincareConjecture.Proofs.M38.LocalCapBoundary
import PoincareConjecture.Proofs.M38.PolarCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M38

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}
  {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
  {I : MetricSurgeryInput K g} (R : MetricSurgeryResult g₀ I)

theorem local_collapse_inverse_image_open {U : Set R.output.carrier}
    (hU : IsOpen U)
    (hsub : U ⊆ R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1) :
    IsOpen (R.retained_inverse '' U) := by
  have hleft : Set.LeftInvOn R.collapse R.retained_inverse
      (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1) := by
    rintro y ⟨x, _, rfl⟩
    exact R.retained_right_inverse ⟨x, rfl⟩
  have hinv : ContMDiffOn (𝓡 3) (𝓡 3) ∞ R.collapse
      (R.retained_inverse '' (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1)) := by
    apply R.retained_smooth.mono
    rintro x ⟨y, hy, rfl⟩
    exact local_collapse_inverse_mem R hy
  exact smooth_left_inverse_image_open (local_collapse_collar_open R)
    R.retained_inverse_smooth hinv hleft hU hsub

noncomputable def localCapCollar (r c : ℝ) : RoundCylinderSpace → M :=
  R.retained_inverse ∘ R.cap_map ∘ capShellMap r c

noncomputable def localCapCollarInverse (r c : ℝ) : M → RoundCylinderSpace :=
  capShellInverse r c ∘ R.cap_inverse ∘ R.collapse

variable {r c : ℝ} (hc : 0 < c) (hcr : c < r)
  (hdom : {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} ⊆
    g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5) ∩
      R.cap_map ⁻¹' (R.collapse '' I.neck.region (-I.neck.epsilon⁻¹) 1))

include hc hcr hdom

theorem local_cap_collar_mem {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    localCapCollar R r c z ∈ I.neck.region (-I.neck.epsilon⁻¹) 1 :=
  local_collapse_inverse_mem R (hdom (capShell_mem hc hcr hz)).2

theorem local_cap_collar_collapse {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    R.collapse (localCapCollar R r c z) = R.cap_map (capShellMap r c z) := by
  apply R.retained_right_inverse
  obtain ⟨x, _, hx⟩ := (hdom (capShell_mem hc hcr hz)).2
  exact ⟨x, hx⟩

theorem local_cap_collar_coordinates {z : RoundCylinderSpace}
    (hz : z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :
    R.cap_inverse (R.collapse (localCapCollar R r c z)) = capShellMap r c z := by
  rw [local_cap_collar_collapse R hc hcr hdom hz]
  exact R.cap_left_inverse (hdom (capShell_mem hc hcr hz)).1

theorem local_cap_collar_smooth :
    ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (localCapCollar R r c)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  apply R.retained_inverse_smooth.comp
    (R.cap_map_smooth.comp (capShellMap_smooth r c).contMDiffOn ?_) ?_
  · exact fun z hz => (hdom (capShell_mem hc hcr hz)).1
  · exact fun z hz => (hdom (capShell_mem hc hcr hz)).2

theorem local_cap_collar_left_inverse :
    Set.LeftInvOn (localCapCollarInverse R r c) (localCapCollar R r c)
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  intro z hz
  change capShellInverse r c (R.cap_inverse (R.collapse (localCapCollar R r c z))) = z
  rw [local_cap_collar_coordinates R hc hcr hdom hz]
  exact capShell_left_inverse hc hcr hz

theorem local_cap_collar_right_inverse :
    Set.LeftInvOn (localCapCollar R r c) (localCapCollarInverse R r c)
      (localCapCollar R r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rintro x ⟨z, hz, rfl⟩
  exact congrArg (localCapCollar R r c) (local_cap_collar_left_inverse R hc hcr hdom hz)

theorem local_cap_collar_inverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (localCapCollarInverse R r c)
      (localCapCollar R r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  have hsource : localCapCollar R r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) ⊆
      I.neck.region (-I.neck.epsilon⁻¹) 1 := by
    rintro x ⟨z, hz, rfl⟩
    exact local_cap_collar_mem R hc hcr hdom hz
  have hcap : Set.MapsTo R.collapse
      (localCapCollar R r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1))
      (R.cap_map '' g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) := by
    rintro x ⟨z, hz, rfl⟩
    rw [local_cap_collar_collapse R hc hcr hdom hz]
    exact Set.mem_image_of_mem R.cap_map (hdom (capShell_mem hc hcr hz)).1
  apply (capShellInverse_smooth r c).comp
    (R.cap_inverse_smooth.comp (R.retained_smooth.mono hsource) hcap)
  rintro x ⟨z, hz, rfl⟩
  change R.cap_inverse (R.collapse (localCapCollar R r c z)) ≠ 0
  rw [local_cap_collar_coordinates R hc hcr hdom hz]
  apply norm_pos_iff.mp
  have h := capShell_mem hc hcr hz
  linarith [h.1]

theorem local_cap_collar_open :
    IsOpen (localCapCollar R r c '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  have hopen : IsOpen {x : StandardCapSpace | r - c < ‖x‖ ∧ ‖x‖ < r + c} :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  change IsOpen ((R.retained_inverse ∘ R.cap_map ∘ capShellMap r c) '' _)
  rw [Set.image_comp, Set.image_comp, capShell_image hc hcr]
  apply local_collapse_inverse_image_open R
    (local_cap_image_open R hopen (fun x hx => (hdom hx).1))
  rintro y ⟨x, hx, rfl⟩
  exact (hdom hx).2

theorem local_cap_collar_negative {z : UnitTwoSphere} {s : ℝ}
    (hs : s ∈ Set.Ioo (-1 : ℝ) 0)
    (hball : g₀.metric.ball 0 (g₀.cylindrical_end.radius + 4) = Metric.ball 0 r)
    (hclosed : Metric.closedBall 0 r ⊆ g₀.metric.ball 0 (g₀.cylindrical_end.radius + 5)) :
    localCapCollar R r c (z, s) ∈ I.neck.region (-I.neck.epsilon⁻¹) 0 := by
  have hz : (z, s) ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    ⟨Set.mem_univ _, hs.1, hs.2.trans zero_lt_one⟩
  apply (local_cap_exterior_inverse R (hc.trans hcr) hball hclosed
    (hdom (capShell_mem hc hcr hz)).1 ?_).1
  rw [Metric.mem_closedBall, dist_zero_right, capShell_norm hc hcr hz]
  have hcs : c * s < 0 := mul_neg_of_pos_of_neg hc hs.2
  linarith

end PoincareConjecture.M38

import PoincareLib.Topology.Manifold.NeckCap.Models
import PoincareLib.Topology.Manifold.Surgery.Event.Monodromy.MonodromyAtlas
import PoincareLib.Topology.Manifold.Surgery.Event.Circle.CircleCoordinates

/-!
# The actual circle projection of the monodromy quotient

Exponential polar coordinates identify the puncture with the sphere
cylinder. Log radius modulo integers descends to the literal quotient
and is smooth through its already constructed inverse sheets.
-/

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareMT.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩

/-- The point with the prescribed sphere direction and real log radius. -/
noncomputable def monodromyPolarPoint (p : RoundCylinderSpace) : monodromyPunctureOpen :=
  ⟨Real.exp p.2 • p.1.val, by
    apply norm_pos_iff.mp
    simpa [norm_smul] using Real.exp_pos p.2⟩

/-- Its actual Euclidean radius is the exponential of the real parameter. -/
theorem monodromyPolarPoint_norm (p : RoundCylinderSpace) :
    ‖(monodromyPolarPoint p).val‖ = Real.exp p.2 := by
  simp [monodromyPolarPoint, norm_smul]

/-- Exponential polar coordinates have the specified log radius. -/
theorem monodromyPolarPoint_logRadius (p : RoundCylinderSpace) :
    monodromyLogRadius (monodromyPolarPoint p) = p.2 := by
  rw [monodromyLogRadius, monodromyPolarPoint_norm, Real.log_exp]

/-- Exponential polar coordinates have the specified sphere direction. -/
theorem monodromyPolarPoint_direction (p : RoundCylinderSpace) :
    capUnitDirection (monodromyPolarPoint p).val = p.1 :=
  capUnitDirection_smul p.1 (Real.exp_pos p.2)

/-- Direction and log radius reconstruct the original nonzero Euclidean point. -/
theorem monodromyPolarPoint_reconstruct (x : monodromyPunctureOpen) :
    monodromyPolarPoint (capUnitDirection x.val, monodromyLogRadius x) = x := by
  apply Subtype.ext
  change Real.exp (Real.log ‖x.val‖) • (capUnitDirection x.val).val = x.val
  rw [Real.exp_log (norm_pos_iff.mpr x.property)]
  exact capUnitDirection_radial x.val

/-- The actual exponential polar map is smooth in the inherited puncture atlas. -/
theorem monodromyPolarPoint_smooth :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ monodromyPolarPoint := by
  apply (ContMDiff.subtypeVal_comp_iff monodromyPunctureOpen _).mp
  exact (Real.contDiff_exp.contMDiff.comp contMDiff_snd).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold

local notation "mq" => (Quotient.mk (monodromyOrbitRel phi) :
  monodromyPunctureOpen → MonodromyQuotient phi)

/-- Log radius modulo its integer translations gives a well-defined
projection from the literal orbit quotient to the literal unit circle. -/
noncomputable def monodromyProjection : MonodromyQuotient phi → UnitCircle :=
  Quotient.lift (fun x => circlePeriodMap (monodromyLogRadius x)) (by
    intro x y hxy
    obtain ⟨n, hn⟩ := (monodromy_quotient_eq_iff phi x y).mp (Quotient.sound hxy)
    rw [← hn, monodromyDeck_logRadius]
    exact (circlePeriodMap_eq_iff _ _).mpr ⟨n, by ring⟩)

/-- On every actual representative the projection is its log-radius angle. -/
theorem monodromyProjection_mk (x : monodromyPunctureOpen) :
    monodromyProjection phi (mq x) = circlePeriodMap (monodromyLogRadius x) := rfl

/-- Continuity descends along the same open quotient map. -/
theorem monodromyProjection_continuous : Continuous (monodromyProjection phi) :=
  (monodromy_open_quotient phi).isQuotientMap.continuous_iff.mpr
    (circlePeriodMap_smooth.continuous.comp monodromyLogRadius_smooth.continuous)

/-- The actual projection is smooth by its expression through each
already proved smooth local inverse covering sheet. -/
theorem monodromyProjection_smooth :
    ContMDiff (𝓡 3) (𝓡 1) ∞ (monodromyProjection phi) := by
  intro p
  let s := (monodromy_quotient_localHomeomorph phi).localInverseAt
    (monodromyRepresentative phi p)
  have hp : p ∈ s.source := by
    rw [← monodromyRepresentative_spec phi p]
    exact (monodromy_quotient_localHomeomorph phi).apply_self_mem_localInverseAt_source
  have hs := monodromy_chosen_sheet_contMDiffAt phi p
  have hlog := monodromyLogRadius_smooth.contMDiffAt.comp p hs
  have hc := circlePeriodMap_smooth.contMDiffAt.comp p hlog
  apply hc.congr_of_eventuallyEq
  filter_upwards [s.open_source.mem_nhds hp] with q hq
  have heq : mq (s q) = q :=
    (monodromy_quotient_localHomeomorph phi).apply_localInverseAt_of_mem hq
  change monodromyProjection phi q = circlePeriodMap (monodromyLogRadius (s q))
  exact (congrArg (monodromyProjection phi) heq).symm

/-- Every base point has a representative with its chosen real log radius. -/
theorem monodromyProjection_surjective : Function.Surjective (monodromyProjection phi) := by
  intro b
  obtain ⟨s, hs⟩ := circlePeriodMap_surjective b
  let z := capUnitDirection (0 : StandardCapSpace)
  refine ⟨mq (monodromyPolarPoint (z, s)), ?_⟩
  rw [monodromyProjection_mk, monodromyPolarPoint_logRadius]
  exact hs

end PoincareMT.M38

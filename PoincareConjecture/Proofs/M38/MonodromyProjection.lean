import PoincareConjecture.Proofs.M38.MonodromyAtlas
import PoincareConjecture.Proofs.M38.CircleCoordinates









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp [StandardCapSpace]⟩


noncomputable def monodromyPolarPoint (p : RoundCylinderSpace) : monodromyPunctureOpen :=
  ⟨Real.exp p.2 • p.1.val, by
    apply norm_pos_iff.mp
    simpa [norm_smul] using Real.exp_pos p.2⟩


theorem monodromyPolarPoint_norm (p : RoundCylinderSpace) :
    ‖(monodromyPolarPoint p).val‖ = Real.exp p.2 := by
  simp [monodromyPolarPoint, norm_smul]


theorem monodromyPolarPoint_logRadius (p : RoundCylinderSpace) :
    monodromyLogRadius (monodromyPolarPoint p) = p.2 := by
  rw [monodromyLogRadius, monodromyPolarPoint_norm, Real.log_exp]


theorem monodromyPolarPoint_direction (p : RoundCylinderSpace) :
    capUnitDirection (monodromyPolarPoint p).val = p.1 :=
  capUnitDirection_smul p.1 (Real.exp_pos p.2)


theorem monodromyPolarPoint_reconstruct (x : monodromyPunctureOpen) :
    monodromyPolarPoint (capUnitDirection x.val, monodromyLogRadius x) = x := by
  apply Subtype.ext
  change Real.exp (Real.log ‖x.val‖) • (capUnitDirection x.val).val = x.val
  rw [Real.exp_log (norm_pos_iff.mpr x.property)]
  exact capUnitDirection_radial x.val


theorem monodromyPolarPoint_smooth :
    ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ monodromyPolarPoint := by
  apply (ContMDiff.subtypeVal_comp_iff monodromyPunctureOpen _).mp
  exact (Real.contDiff_exp.contMDiff.comp contMDiff_snd).smul
    (contMDiff_coe_sphere.comp contMDiff_fst)

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold

local notation "mq" => (Quotient.mk (monodromyOrbitRel phi) :
  monodromyPunctureOpen → MonodromyQuotient phi)



noncomputable def monodromyProjection : MonodromyQuotient phi → UnitCircle :=
  Quotient.lift (fun x => circlePeriodMap (monodromyLogRadius x)) (by
    intro x y hxy
    obtain ⟨n, hn⟩ := (monodromy_quotient_eq_iff phi x y).mp (Quotient.sound hxy)
    rw [← hn, monodromyDeck_logRadius]
    exact (circlePeriodMap_eq_iff _ _).mpr ⟨n, by ring⟩)


theorem monodromyProjection_mk (x : monodromyPunctureOpen) :
    monodromyProjection phi (mq x) = circlePeriodMap (monodromyLogRadius x) := rfl


theorem monodromyProjection_continuous : Continuous (monodromyProjection phi) :=
  (monodromy_open_quotient phi).isQuotientMap.continuous_iff.mpr
    (circlePeriodMap_smooth.continuous.comp monodromyLogRadius_smooth.continuous)



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


theorem monodromyProjection_surjective : Function.Surjective (monodromyProjection phi) := by
  intro b
  obtain ⟨s, hs⟩ := circlePeriodMap_surjective b
  let z := capUnitDirection (0 : StandardCapSpace)
  refine ⟨mq (monodromyPolarPoint (z, s)), ?_⟩
  rw [monodromyProjection_mk, monodromyPolarPoint_logRadius]
  exact hs

end PoincareConjecture.M38

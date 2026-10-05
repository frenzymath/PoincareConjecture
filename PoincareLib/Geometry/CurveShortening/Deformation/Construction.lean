import PoincareLib.Geometry.CurveShortening.Deformation.Assembly
import PoincareLib.Geometry.CurveShortening.Deformation.Profile.AreaComparisonProfile
import PoincareLib.Geometry.CurveShortening.Deformation.Transfer.NetConclusion
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Infimum.FreeClassInfimum
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Continuity

/-!
# Exact predecessor and endpoint assembly

Only the raw M61 width fields are needed by the concrete M65 wrapper.
For a zero-duration slab the original family itself gives the required
deformation, without strengthening the frozen time-order hypothesis.
MT Definition 18.17 and Proposition 18.24; derivation 51.
For positive duration the actual common terminal estimate supplies the
last field of the projected-family construction.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- The proved M61 raw-width adapters use the proved filling service
directly. No based class-label system is needed by this raw core.
MT Definition 18.17, p. 430; derivation 51. -/
theorem m65RawWidthCore_from_closed_predecessors : M61RawWidthCore.{u} := by
  constructor
  · intro M _ _ _ _ _ g hcompact F hnull
    exact m61FamilyWidth_from_M60 g (m60FillingAreaProperties_of_compact g hcompact) F hnull
  · intro M _ _ _ _ _ g hcompact F hnull
    exact m61FreeClassWidth_from_M60 g (m60FillingAreaProperties_of_compact g hcompact) F hnull

/-- At equal endpoints the original family satisfies every frozen
deformation field, using the literal initial-value identity for the
canonical profile. MT Proposition 18.24; derivation 51. -/
def m65ZeroDurationDeformedFamily
    {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {a zeta : ℝ}
    (P : M65RawFlowInput M a a) (hzeta : 0 < zeta) : M65DeformedFamily M P zeta where
  family := fun _ => P.family
  family_continuous := P.family.continuous.comp continuous_snd
  null := fun _ => P.family_null
  free_homotopy_to_initial := fun _ => ContinuousMap.Homotopic.refl P.family
  initial_area_close := fun _ => by simpa only [sub_self, abs_zero] using hzeta
  terminal_alternative := fun _ => Or.inr (by
    rw [areaComparisonProfile_initial]
    exact le_add_of_nonneg_right hzeta.le)

/-- The complete deformation for the exact raw input and any selected
predecessor record. The terminal estimate is supplied by the proved
analytic chain, and equal endpoints retain the original family.
MT Proposition 18.24, pp. 433-434 and 464; derivation 51. -/
theorem m65Construction
    (hM61 : M61RawWidthCore.{u}) (hM64 : M64ComparisonTheory.{u})
    (M : Type u) [TopologicalSpace M] [ChartedSpace LoopAmbient M]
    [IsManifold (𝓡 3) ∞ M] {a b : ℝ} (P : M65RawFlowInput M a b)
    (H : M65Predecessors M P) : Nonempty (M65Conclusion M P H) := by
  classical
  let : T2Space M := P.hausdorff
  let : SecondCountableTopology M := P.second_countable
  refine ⟨{ deformation := ?_ }⟩
  intro zeta hzeta
  rcases lt_or_eq_of_le P.time_ordered with hab | hab
  · obtain ⟨N, _, hN⟩ := H.m64.approximation P.family P.family_null zeta hzeta
    obtain ⟨Q⟩ := hN N le_rfl
    obtain ⟨circumference, h, _, terminal⟩ :=
      m65CommonTerminalAlternative_proved hM61 hM64 P.compact H.m64
        Q.family Q.estimates hab hzeta
    exact ⟨m65DeformedFamilyOfProjectedEstimate (P := P)
      (Q.family.solutions circumference h) terminal⟩
  · subst b
    exact ⟨m65ZeroDurationDeformedFamily P hzeta⟩

end PoincareMT

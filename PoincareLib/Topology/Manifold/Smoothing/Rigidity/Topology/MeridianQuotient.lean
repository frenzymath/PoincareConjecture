import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Levels.MeridianCut
import Mathlib.Topology.Separation.Hausdorff

/-!
# The whole compact meridian cut as an actual quotient

The original cut projection is a quotient map. Its exact fibers
retain both complete end faces, and its old-boundary preimage
is the entire original rim cylinder. See derivation 005.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 1)
local notation "H" => LatticeHandle (Fin 2) (Fin 1) L
local notation "B" => latticeHandleBoundary (Fin 2) (Fin 1) L
local notation "p" => (4 * (128 : ℝ))

/-- The entire closed cut, retaining both end parameters.
See rigidity derivation 005. -/
abbrev HamiltonMeridianClosedCut := D × Icc (0 : ℝ) p

/-- Restriction of the already constructed total cut map to
its whole compact carrier. See rigidity derivation 005. -/
noncomputable def hamiltonMeridianQuotient : C(HamiltonMeridianClosedCut, H) :=
  hamiltonMeridianCutMap.comp
    ⟨fun z => (z.1, (z.2 : ℝ)),
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)⟩

/-- The whole closed cut covers the original handle.
See rigidity derivation 005. -/
theorem hamiltonMeridianQuotient_surjective :
    Function.Surjective hamiltonMeridianQuotient := by
  intro z
  have hz : z ∈ hamiltonMeridianCutMap '' (univ ×ˢ Icc (0 : ℝ) p) :=
    hamiltonMeridianCutMap_image.symm.subset (mem_univ z)
  obtain ⟨⟨x, t⟩, ht, he⟩ := hz
  exact ⟨(x, ⟨t, ht.2⟩), he⟩

/-- Compactness and the actual continuous surjection give the
quotient topology, including every end-face point.
See rigidity derivation 005. -/
theorem isQuotientMap_hamiltonMeridianQuotient :
    Topology.IsQuotientMap hamiltonMeridianQuotient := by
  let : T2Space H := ((Homeomorph.refl D).prodCongr
    hamiltonSolidTorusCircleEquiv).isEmbedding.t2Space
  exact hamiltonMeridianQuotient.continuous.isClosedMap.isQuotientMap
    hamiltonMeridianQuotient.continuous hamiltonMeridianQuotient_surjective

/-- The only identifications are the corresponding points of
the two entire end disks. See rigidity derivation 005. -/
theorem hamiltonMeridianQuotient_eq_iff (a b : HamiltonMeridianClosedCut) :
    hamiltonMeridianQuotient a = hamiltonMeridianQuotient b ↔
      a.1 = b.1 ∧ ((a.2 : ℝ) = b.2 ∨
        ((a.2 : ℝ) = 0 ∧ (b.2 : ℝ) = p) ∨
        ((a.2 : ℝ) = p ∧ (b.2 : ℝ) = 0)) :=
  hamiltonMeridianCutMap_eq_iff a.1 b.1 a.2.property b.2.property

/-- The full old boundary is precisely the whole lateral rim
cylinder, without any end-disk interior. See derivation 005. -/
theorem hamiltonMeridianQuotient_mem_boundary (a : HamiltonMeridianClosedCut) :
    hamiltonMeridianQuotient a ∈ B ↔ ‖(a.1 : V2)‖ = 1 := by
  change (‖(a.1 : V2)‖ = 1 ∧ True) ↔ ‖(a.1 : V2)‖ = 1
  exact ⟨And.left, fun h => ⟨h, trivial⟩⟩

end PoincareMT.M76

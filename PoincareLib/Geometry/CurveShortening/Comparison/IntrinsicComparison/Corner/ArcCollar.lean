import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Finite.CornerArcChain

/-! Retain an actual arc collar between two selected finite corner caps.
Source: MT Claim 19.40; normal-collision-transversality derivation, Section 6. -/

noncomputable section
set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT

/-- One concrete chain, its actual cap contacts, and coverage in the original arc parameter.
Source: MT Claim 19.40; normal-collision-transversality derivation, Section 6. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 6. -/
structure M64IntrinsicCornerArcCollar
    {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
    {U : Set AnnulusCoordinates} (C : M64IntrinsicFiniteCornerCaps alpha beta A B U)
    (corner : Bool → J) (sigma : ℝ → AnnulusCoordinates) (T : ℝ) where
  reversed : Bool
  chain : M64IntrinsicArcBandChain (fun t => sigma (if reversed then T - t else t))
    (C.radius (corner (if reversed then true else false)))
    (T - C.radius (corner (if reversed then false else true))) U
  cap_contact : ∀ i, (C.carrier (corner false) ∪ C.carrier (corner true)) ∩
      (chain.band i).carrier =
    (if chain.cut i.castSucc = C.radius (corner (if reversed then true else false))
      then (chain.band i).leftCut else ∅) ∪
      (if chain.cut i.succ = T - C.radius (corner (if reversed then false else true))
        then (chain.band i).rightCut else ∅)
  covered : ∀ p ∈ Icc (0 : ℝ) T,
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ sigma p ∈ W ∧
      W ∩ closure U ⊆ (C.carrier (corner false) ∪ C.carrier (corner true)) ∪
        ⋃ i, (chain.band i).carrier

namespace M64IntrinsicCornerArcCollar

variable {J : Type*} {alpha beta : J → ℝ → AnnulusCoordinates} {A B : J → ℝ}
  {U : Set AnnulusCoordinates} {C : M64IntrinsicFiniteCornerCaps alpha beta A B U}
  {corner : Bool → J} {sigma : ℝ → AnnulusCoordinates} {T : ℝ}
  (D : M64IntrinsicCornerArcCollar C corner sigma T)

/-- The literal finite union of the retained bands. Source: MT Claim 19.40;
normal-collision-transversality derivation, Section 6. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 6. -/
abbrev bands : Set AnnulusCoordinates := ⋃ i, (D.chain.band i).carrier

/-- The actual band union is closed. Source: MT Claim 19.40; normal-collision-transversality
derivation, Section 6. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 6. -/
theorem bands_closed : IsClosed D.bands :=
  isClosed_iUnion_of_finite (fun i => (D.chain.band i).isClosed_carrier)

/-- All actual bands lie on the occupied side. Source: MT Claim 19.40;
normal-collision-transversality derivation, Section 6. Construction:
proof-work/tasks/M64/derivations/2026-09-27-normal-collision-transversality.md, Section 6. -/
theorem bands_occupied : D.bands ⊆ closure U := iUnion_subset D.chain.occupied

end M64IntrinsicCornerArcCollar

end PoincareMT

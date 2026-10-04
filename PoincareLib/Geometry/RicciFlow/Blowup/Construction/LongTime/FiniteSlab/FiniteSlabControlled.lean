import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.Restriction
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.Noncollapse
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Generalized.WorldlineUniqueness

/-!
# Closed controlled cylinders from finite horizon slabs

The finite-horizon contract stores an open-left generalized cylinder and its
pointwise noncollapse certificate.  Once the uniform curvature and defect
estimates from Claims 11.5--11.7 are available on a strictly shorter closed
slab, the data form the `ControlledBlowupCylinder` consumed by the long
compactness assembly.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M30

/-- A controlled cylinder together with the original parabolic noncollapse
certificate on its source ball.  The projected `ControlledBlowupCylinder`
used by the geometric compactness assembly intentionally omits this field;
this wrapper keeps it available for the later volume-transfer step. -/
structure NoncollapsedControlledBlowupCylinder
    (S : GeneralizedBlowupSequence.{u})
    (k : ℕ) (A T B eta kappa r₀ : ℝ) extends
    ControlledBlowupCylinder S k A T B eta where
  noncollapsed : ∀ s (hs : s ∈ Set.Icc (-T) 0)
    (x : ((S.flow k).slice (S.base k).1).carrier),
    x ∈ S.baseBall k A →
    GeneralizedKappaNoncollapsedAt
      (S.flow k) (embedding.pointMap s hs x) kappa r₀

/-- Restrict a finite-horizon slab and attach the two explicit normalized
curvature estimates required by the growing-source assembly. -/
noncomputable def controlledCylinderOfFiniteHorizonSlab
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ}
    {A T T' kappa r₀ B eta : ℝ}
    (e : M30FiniteHorizonSlab S k A T kappa r₀) (hT : T' < T)
    (hcurv : ∀ s (hs : s ∈ Icc (-T') 0)
      (x : ((S.flow k).slice (S.base k).1).carrier),
      x ∈ S.baseBall k A →
      |(S.flow k).curvatureNorm
        ((FiniteHorizonSlab.closedEmbedding e hT).pointMap s hs x)| ≤
        B * S.scale k)
    (hdefect : ∀ s (hs : s ∈ Icc (-T') 0)
      (x : ((S.flow k).slice (S.base k).1).carrier),
      x ∈ S.baseBall k A →
      let p := (FiniteHorizonSlab.closedEmbedding e hT).pointMap s hs x
      ((S.flow k).connection p.1).negativeCurvaturePart p.2 ≤ eta * S.scale k) :
    ControlledBlowupCylinder S k A T' B eta := {
  embedding := FiniteHorizonSlab.closedEmbedding e hT
  zero_identity := fun h₀ x hx =>
    FiniteHorizonSlab.closedEmbedding_zero_identity e hT h₀ x hx
  curvature_bound := fun s hs x hx => hcurv s hs x hx
  negative_curvature_bound := fun s hs x hx => hdefect s hs x hx }

/-- The finite-slab certificate survives the same restriction used by the
controlled-cylinder projection. -/
noncomputable def noncollapsedControlledCylinderOfFiniteHorizonSlab
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ}
    {A T T' kappa r₀ B eta : ℝ}
    (e : M30FiniteHorizonSlab S k A T kappa r₀) (hT : T' < T)
    (hcurv : ∀ s (hs : s ∈ Icc (-T') 0)
      (x : ((S.flow k).slice (S.base k).1).carrier),
      x ∈ S.baseBall k A →
      |(S.flow k).curvatureNorm
        ((FiniteHorizonSlab.closedEmbedding e hT).pointMap s hs x)| ≤
        B * S.scale k)
    (hdefect : ∀ s (hs : s ∈ Icc (-T') 0)
      (x : ((S.flow k).slice (S.base k).1).carrier),
      x ∈ S.baseBall k A →
      let p := (FiniteHorizonSlab.closedEmbedding e hT).pointMap s hs x
      ((S.flow k).connection p.1).negativeCurvaturePart p.2 ≤ eta * S.scale k) :
    NoncollapsedControlledBlowupCylinder S k A T' B eta kappa r₀ := {
  embedding := FiniteHorizonSlab.closedEmbedding e hT
  zero_identity := fun h₀ x hx =>
    FiniteHorizonSlab.closedEmbedding_zero_identity e hT h₀ x hx
  curvature_bound := fun s hs x hx => hcurv s hs x hx
  negative_curvature_bound := fun s hs x hx => hdefect s hs x hx
  noncollapsed := fun s hs x hx =>
    FiniteHorizonSlab.closedEmbedding_noncollapsed e hT s hs x hx }

/-- Worldline uniqueness transfers a retained certificate to another
controlled cylinder with the same source ball, slab, and terminal identity. -/
theorem ControlledBlowupCylinder.noncollapsed_of_noncollapsed
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ}
    {A T B eta kappa r₀ : ℝ}
    (E : ControlledBlowupCylinder S k A T B eta)
    (N : NoncollapsedControlledBlowupCylinder S k A T B eta kappa r₀)
    (hT : 0 < T) :
    ∀ s (hs : s ∈ Icc (-T) 0)
      (x : ((S.flow k).slice (S.base k).1).carrier),
      x ∈ S.baseBall k A →
      GeneralizedKappaNoncollapsedAt
        (S.flow k) (E.embedding.pointMap s hs x) kappa r₀ := by
  intro s hs x hx
  have hzero : (0 : ℝ) ∈ Icc (-T) 0 := ⟨by linarith, le_rfl⟩
  have hne : (Icc (-T) (0 : ℝ)).Nontrivial :=
    ⟨-T, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
  have hmeet : E.embedding.pointMap 0 hzero x = N.embedding.pointMap 0 hzero x :=
    (E.zero_identity hzero x hx).trans (N.zero_identity hzero x hx).symm
  have hpoint := Cylinder.pointMap_eq_on_overlap E.embedding N.embedding
    ordConnected_Icc ordConnected_Icc hx hx hzero hzero hmeet s hs hs
  rw [hpoint]
  exact N.noncollapsed s hs x hx

/-- The same transfer remains valid after weakening the source certificate. -/
theorem ControlledBlowupCylinder.noncollapsed_of_noncollapsed_mono
    {S : GeneralizedBlowupSequence.{u}} {k : ℕ}
    {A T B eta kappa r₀ kappa' r₀' : ℝ}
    (E : ControlledBlowupCylinder S k A T B eta)
    (N : NoncollapsedControlledBlowupCylinder S k A T B eta kappa r₀)
    (hT : 0 < T) (hkappa : kappa' ≤ kappa) (hr₀ : r₀' ≤ r₀) :
    ∀ s (hs : s ∈ Set.Icc (-T) 0)
      (x : ((S.flow k).slice (S.base k).1).carrier),
      x ∈ S.baseBall k A →
      GeneralizedKappaNoncollapsedAt
        (S.flow k) (E.embedding.pointMap s hs x) kappa' r₀' := by
  intro s hs x hx
  exact GeneralizedKappaNoncollapsedAt.mono_radius
    (GeneralizedKappaNoncollapsedAt.mono_kappa
      (ControlledBlowupCylinder.noncollapsed_of_noncollapsed E N hT s hs x hx)
      hkappa) hr₀

end PoincareMT.M30

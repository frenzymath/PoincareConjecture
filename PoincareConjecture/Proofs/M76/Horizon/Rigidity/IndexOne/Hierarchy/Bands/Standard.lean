import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Disks.StandardMeridian
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Bands.Pullback
import PoincareConjecture.Proofs.M76.Mathlib.AddCircleShortArcCharts









set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p

private instance : Fact (0 < p) := ⟨by norm_num⟩
private instance : T2Space X := ((Homeomorph.refl (Fin 1 → ℝ)).prodCongr
  (hamiltonLowerLatticePiEquiv (Fin 2))).isEmbedding.t2Space
private instance : CompactSpace (Q ×ˢ I) :=
  isCompact_iff_compactSpace.mp ((isCompact_sphere (0 : V2) 1).prod isCompact_Icc)


noncomputable def standardMeridianBandParameter (a b : ℝ) (z : V2 × ℝ) : X :=
  ((fun _ => z.1 0), QuotientAddGroup.mk ![z.2, (b - a) * (z.1 1 + 1) / 2 + a])

theorem continuous_standardMeridianBandParameter (a b : ℝ) :
    Continuous (standardMeridianBandParameter a b) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro i
    exact (continuous_apply 0).comp continuous_fst
  · apply QuotientAddGroup.continuous_mk.comp
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

theorem standardMeridianBandParameter_eq_boundary (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) (z : Q) (t : ℝ) :
    standardMeridianBandParameter a b (z, t) =
      (standardSlabBoundaryCoordinates a b hab hshort (z, (t : C)) : X) :=
  (standardSlabBoundaryCoordinates_coe a b hab hshort z t).symm

theorem mapsTo_standardMeridianBandParameter_frontier (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) :
    MapsTo (standardMeridianBandParameter a b) (Q ×ˢ (univ : Set ℝ))
      (frontier (sourceSlab (ContinuousMap.id H) a b)) := by
  intro z hz
  rw [standardMeridianBandParameter_eq_boundary a b hab hshort ⟨z.1, hz.1⟩ z.2]
  exact (standardSlabBoundaryCoordinates a b hab hshort (⟨z.1, hz.1⟩, (z.2 : C))).property

theorem injOn_standardMeridianBandParameter (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) : InjOn (standardMeridianBandParameter a b) (Q ×ˢ I) := by
  intro z hz w hw hzw
  rw [standardMeridianBandParameter_eq_boundary a b hab hshort ⟨z.1, hz.1⟩ z.2,
    standardMeridianBandParameter_eq_boundary a b hab hshort ⟨w.1, hw.1⟩ w.2] at hzw
  have hh := (standardSlabBoundaryCoordinates a b hab hshort).injective (Subtype.ext hzw)
  have hf : z.1 = w.1 := congrArg (fun x : Q × C => (x.1 : V2)) hh
  have ht : (z.2 : C) = (w.2 : C) := congrArg Prod.snd hh
  have hzI : z.2 ∈ Ico (-1 : ℝ) (-1 + p) := ⟨hz.2.1, by linarith [hz.2.2]⟩
  have hwI : w.2 ∈ Ico (-1 : ℝ) (-1 + p) := ⟨hw.2.1, by linarith [hw.2.2]⟩
  exact Prod.ext hf ((AddCircle.coe_eq_coe_iff_of_mem_Ico hzI hwI).mp ht)

def standardMeridianBand (a b : ℝ) : Set X :=
  standardMeridianBandParameter a b '' (Q ×ˢ I)

def standardMeridianOpenBand (a b : ℝ) : Set X :=
  standardMeridianBandParameter a b '' (Q ×ˢ Ioo (-1 : ℝ) 1)


noncomputable def standardMeridianBandCoordinates (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) : (Q ×ˢ I) ≃ₜ standardMeridianBand a b :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn (standardMeridianBandParameter a b) (Q ×ˢ I)
      (injOn_standardMeridianBandParameter a b hab hshort))
    (((continuous_standardMeridianBandParameter a b).comp continuous_subtype_val).subtype_mk _)

theorem standardMeridianBandCoordinates_apply (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) (z : Q ×ˢ I) :
    (standardMeridianBandCoordinates a b hab hshort z : X) =
      standardMeridianBandParameter a b z := rfl

theorem standardMeridianBand_subset_frontier (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) :
    standardMeridianBand a b ⊆ frontier (sourceSlab (ContinuousMap.id H) a b) := by
  rintro _ ⟨z, hz, rfl⟩
  exact mapsTo_standardMeridianBandParameter_frontier a b hab hshort ⟨hz.1, mem_univ _⟩


theorem isOpen_standardMeridianOpenBand (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) :
    IsOpen ((Subtype.val : frontier (sourceSlab (ContinuousMap.id H) a b) → X) ⁻¹'
      standardMeridianOpenBand a b) := by
  let T := standardSlabBoundaryCoordinates a b hab hshort
  let arc := AddCircle.shortArcQuotient p 1
  have heq : (Subtype.val : frontier (sourceSlab (ContinuousMap.id H) a b) → X) ⁻¹'
      standardMeridianOpenBand a b = (fun y => (T.symm y).2) ⁻¹' arc.target := by
    ext y
    constructor
    · rintro ⟨z, hz, hzy⟩
      rw [standardMeridianBandParameter_eq_boundary a b hab hshort ⟨z.1, hz.1⟩ z.2] at hzy
      have hy : y = T (⟨z.1, hz.1⟩, (z.2 : C)) := (Subtype.ext hzy).symm
      change (T.symm y).2 ∈ arc.target
      rw [hy, T.symm_apply_apply]
      rw [AddCircle.shortArcQuotient_target p (by norm_num)]
      exact ⟨z.2, hz.2, rfl⟩
    · intro hy
      change (T.symm y).2 ∈ arc.target at hy
      rw [AddCircle.shortArcQuotient_target p (by norm_num)] at hy
      obtain ⟨t, ht, hty⟩ := hy
      refine ⟨((T.symm y).1, t), ⟨(T.symm y).1.property, ht⟩, ?_⟩
      rw [standardMeridianBandParameter_eq_boundary a b hab hshort (T.symm y).1 t,
        hty, Prod.eta, T.apply_symm_apply]
  rw [heq]
  exact arc.open_target.preimage (continuous_snd.comp T.symm.continuous)

theorem standardMeridianBand_interior_eq (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) :
    cylinderBandInterior (standardMeridianBandCoordinates a b hab hshort) =
      standardMeridianOpenBand a b := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, ⟨z.property.1, hz⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2⟩, hz.2, rfl⟩


noncomputable def standardMeridianBandFilling (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) : C(D, sourceSlab (ContinuousMap.id H) a b) :=
  ⟨fun x => standardSlabMeridianCoordinates a b hab hshort (x, 0),
    (standardSlabMeridianCoordinates a b hab hshort).continuous.comp
      (continuous_id.prodMk continuous_const)⟩

theorem standardMeridianBandFilling_boundary (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) (x : Q) :
    (standardMeridianBandFilling a b hab hshort
      ⟨x, sphere_subset_closedBall x.property⟩ : X) =
      cylinderZeroSection (standardMeridianBandCoordinates a b hab hshort) x := by
  change (standardSlabMeridianCoordinates a b hab hshort
    (⟨x, sphere_subset_closedBall x.property⟩, (0 : C)) : X) = _
  rw [← AddCircle.coe_zero, standardSlabMeridianCoordinates_coe]
  rfl


noncomputable def standardMeridianBandProjection (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) : C(frontier (sourceSlab (ContinuousMap.id H) a b), Q) :=
  ⟨fun x => ((standardSlabBoundaryCoordinates a b hab hshort).symm x).1,
    continuous_fst.comp (standardSlabBoundaryCoordinates a b hab hshort).symm.continuous⟩

theorem standardMeridianBandProjection_apply (a b : ℝ) (hab : a < b)
    (hshort : b < a + p) (x : Q ×ˢ I) :
    standardMeridianBandProjection a b hab hshort
      ⟨standardMeridianBandCoordinates a b hab hshort x,
        standardMeridianBand_subset_frontier a b hab hshort
          (standardMeridianBandCoordinates a b hab hshort x).property⟩ =
      ⟨x.val.1, x.property.1⟩ := by
  have heq : (⟨standardMeridianBandCoordinates a b hab hshort x,
      standardMeridianBand_subset_frontier a b hab hshort
        (standardMeridianBandCoordinates a b hab hshort x).property⟩ :
      frontier (sourceSlab (ContinuousMap.id H) a b)) =
      standardSlabBoundaryCoordinates a b hab hshort
        (⟨x.val.1, x.property.1⟩, (x.val.2 : C)) := by
    apply Subtype.ext
    exact standardMeridianBandParameter_eq_boundary a b hab hshort
      ⟨x.val.1, x.property.1⟩ x.val.2
  change ((standardSlabBoundaryCoordinates a b hab hshort).symm _).1 = _
  rw [heq, Homeomorph.symm_apply_apply]

end PoincareConjecture.M76.HamiltonIntervalTorus

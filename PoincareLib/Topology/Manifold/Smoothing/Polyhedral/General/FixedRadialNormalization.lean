import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.RadialEmbeddingNormalization

/-!
# Radial normalization relative to prescribed unit vertices

The radial deformation restricts to realizations fixing any chosen set
of unit vertex positions. It gives a homotopy equivalence with their
unit-vertex subspace. This is the fixed-simplex version of Cairns 1940,
Lemma 5.3, pp. 801--802; see M76 derivation 24.
-/

set_option autoImplicit false

open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial realizations with prescribed values on selected labels.
See Cairns p. 801 and M76 derivation 24. -/
abbrev FixedRadialEmbedding (A : AbstractSimplicialComplex ι) (s : Set ι) (w : ι → E) :=
  {v : A.RadialEmbedding E // EqOn v.val w s}

/-- Unit radial realizations with the same selected vertex values.
See Cairns p. 801 and M76 derivation 24. -/
abbrev FixedUnitRadialEmbedding (A : AbstractSimplicialComplex ι) (s : Set ι) (w : ι → E) :=
  {v : A.UnitRadialEmbedding E // EqOn v.val.val w s}

variable {A : AbstractSimplicialComplex ι} {s : Set ι} {w : ι → E}

/-- Normalize a constrained realization while retaining each prescribed
unit coordinate. See Cairns Lemma 5.3 and M76 derivation 24. -/
noncomputable def FixedRadialEmbedding.normalized (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (v : A.FixedRadialEmbedding s w) : A.FixedUnitRadialEmbedding s w :=
  ⟨⟨v.val.normalized, v.val.norm_normalized⟩, by
    intro i hi
    change NormedSpace.normalize (v.val.val i) = w i
    rw [v.property hi, normalize_eq_self_of_norm_eq_one (hw i hi)]⟩

/-- Forget the unit condition while preserving the prescribed values.
See Cairns Lemma 5.3 and M76 derivation 24. -/
def FixedUnitRadialEmbedding.toFixedRadial (v : A.FixedUnitRadialEmbedding s w) :
    A.FixedRadialEmbedding s w := ⟨v.val.val, v.property⟩

/-- Constrained vertex normalization is continuous in vertex topology.
See Cairns p. 801 and M76 derivation 24. -/
theorem FixedRadialEmbedding.continuous_normalized (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Continuous (FixedRadialEmbedding.normalized hw :
      A.FixedRadialEmbedding s w → A.FixedUnitRadialEmbedding s w) :=
  ((RadialEmbedding.continuous_normalized.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- Forgetting the unit condition is continuous.
See Cairns p. 801 and M76 derivation 24. -/
theorem FixedUnitRadialEmbedding.continuous_toFixedRadial :
    Continuous (FixedUnitRadialEmbedding.toFixedRadial :
      A.FixedUnitRadialEmbedding s w → A.FixedRadialEmbedding s w) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- The straight radial deformation preserves all prescribed unit
vertices at every time. See Cairns Lemma 5.3 and M76 derivation 24. -/
noncomputable def FixedRadialEmbedding.interpolate (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (t : I) (v : A.FixedRadialEmbedding s w) : A.FixedRadialEmbedding s w :=
  ⟨v.val.interpolate t, by
    intro i hi
    change (1 - (t : ℝ)) • v.val.val i + (t : ℝ) • NormedSpace.normalize (v.val.val i) = w i
    rw [v.property hi, normalize_eq_self_of_norm_eq_one (hw i hi), ← add_smul]
    simp⟩

/-- The constrained deformation is jointly continuous in time and the
original realization. See Cairns p. 801 and M76 derivation 24. -/
theorem FixedRadialEmbedding.continuous_interpolate (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Continuous (fun tv : I × A.FixedRadialEmbedding s w => tv.2.interpolate hw tv.1) :=
  (RadialEmbedding.continuous_interpolate.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

/-- Radial normalization is a homotopy equivalence relative to any
prescribed collection of unit vertices, including an empty collection.
See Cairns Lemma 5.3 and M76 derivation 24. -/
noncomputable def fixedRadialNormalizationHomotopyEquiv (A : AbstractSimplicialComplex ι)
    (s : Set ι) (w : ι → E) (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    ContinuousMap.HomotopyEquiv (A.FixedRadialEmbedding s w) (A.FixedUnitRadialEmbedding s w) := by
  let f : C(A.FixedRadialEmbedding s w, A.FixedUnitRadialEmbedding s w) :=
    ⟨FixedRadialEmbedding.normalized hw, FixedRadialEmbedding.continuous_normalized hw⟩
  let g : C(A.FixedUnitRadialEmbedding s w, A.FixedRadialEmbedding s w) :=
    ⟨FixedUnitRadialEmbedding.toFixedRadial, FixedUnitRadialEmbedding.continuous_toFixedRadial⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id (A.FixedRadialEmbedding s w)) (g.comp f) :=
    { toFun := fun tv => tv.2.interpolate hw tv.1
      continuous_toFun := FixedRadialEmbedding.continuous_interpolate hw
      map_zero_left := fun v => Subtype.ext v.val.interpolate_zero
      map_one_left := fun v => Subtype.ext v.val.interpolate_one }
  refine ⟨f, g, ⟨H.symm⟩, ?_⟩
  have heq : f.comp g = ContinuousMap.id (A.FixedUnitRadialEmbedding s w) := by
    apply ContinuousMap.ext
    intro v
    exact Subtype.ext (Subtype.ext (v.val.val.normalized_eq_self v.val.property))
  rw [heq]

/-- Contractibility transfers between radial realizations with fixed
unit coordinates and their unit-vertex subspace.
See Cairns pp. 801, 807 and M76 derivation 24. -/
theorem contractible_fixedRadialEmbedding_iff (A : AbstractSimplicialComplex ι)
    (s : Set ι) (w : ι → E) (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    ContractibleSpace (A.FixedRadialEmbedding s w) ↔
      ContractibleSpace (A.FixedUnitRadialEmbedding s w) :=
  (fixedRadialNormalizationHomotopyEquiv A s w hw).contractibleSpace_iff

end AbstractSimplicialComplex

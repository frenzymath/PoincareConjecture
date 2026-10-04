import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.RadialEmbeddingSpace
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Isotopy.RadialRescalingHomotopy
import Mathlib.Topology.Homotopy.Contractible

/-!
# Normalization of radial embedding spaces

The vertex-coordinate space of radial embeddings deforms onto its
unit-vertex subspace. The deformation is jointly continuous in time
and the original embedding and fixes that subspace. This is the radial
deformation in Cairns 1940, Lemma 5.3, pp. 801--802 before taking any
coordinate-change quotient. See M76 derivation 18.
-/

set_option autoImplicit false

open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {A : AbstractSimplicialComplex ι}

/-- Normalize all vertices of a radial embedding. See Cairns
Lemma 5.3, pp. 801--802 and M76 derivation 18. -/
noncomputable def RadialEmbedding.normalized (v : A.RadialEmbedding E) : A.RadialEmbedding E :=
  ⟨fun i => NormedSpace.normalize (v.val i), v.property.normalize⟩

/-- Vertex normalization is continuous in the actual vertex topology.
See Cairns p. 801 and M76 derivation 18. -/
theorem RadialEmbedding.continuous_normalized :
    Continuous (RadialEmbedding.normalized : A.RadialEmbedding E → A.RadialEmbedding E) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_iff_continuousAt.mpr
  intro v
  exact (continuousAt_normalize_of_ne_zero (v.property.ne_zero i)).comp
    (f := fun v : A.RadialEmbedding E => v.val i)
    (((continuous_apply i).comp continuous_subtype_val).continuousAt)

/-- Every vertex of the normalized embedding lies on the unit sphere.
See Cairns p. 801 and M76 derivation 18. -/
theorem RadialEmbedding.norm_normalized (v : A.RadialEmbedding E) (i : ι) :
    ‖v.normalized.val i‖ = 1 := norm_normalize (v.property.ne_zero i)

/-- Normalization fixes an embedding whose vertices are already unit
vectors. See Cairns Lemma 5.3 and M76 derivation 18. -/
theorem RadialEmbedding.normalized_eq_self (v : A.RadialEmbedding E)
    (hv : ∀ i, ‖v.val i‖ = 1) : v.normalized = v :=
  Subtype.ext (funext fun i => normalize_eq_self_of_norm_eq_one (hv i))

/-- Move each vertex along its segment to the unit sphere. Positive
radial scaling keeps the result in the radial embedding space.
See Cairns Lemma 5.3 and M76 derivation 18. -/
noncomputable def RadialEmbedding.interpolate (t : I) (v : A.RadialEmbedding E) :
    A.RadialEmbedding E :=
  ⟨fun i => (1 - (t : ℝ)) • v.val i + (t : ℝ) • NormedSpace.normalize (v.val i), by
    have h := v.property.pos_smul (fun x => 1 - (t : ℝ) + (t : ℝ) * ‖x‖⁻¹)
      (fun i => Geometry.SimplicialComplex.radial_interpolation_pos
        (inv_pos.mpr (norm_pos_iff.mpr (v.property.ne_zero i))) t.property)
    simpa only [add_smul, mul_smul, NormedSpace.normalize] using h⟩

/-- The deformation is continuous simultaneously in time and every
vertex coordinate. See Cairns p. 801 and M76 derivation 18. -/
theorem RadialEmbedding.continuous_interpolate :
    Continuous (fun tv : I × A.RadialEmbedding E => tv.2.interpolate tv.1) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have ht : Continuous (fun tv : I × A.RadialEmbedding E => (tv.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hv : Continuous (fun tv : I × A.RadialEmbedding E => tv.2.val i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  have hn : Continuous (fun tv : I × A.RadialEmbedding E =>
      NormedSpace.normalize (tv.2.val i)) :=
    (continuous_apply i).comp (continuous_subtype_val.comp
      (RadialEmbedding.continuous_normalized.comp continuous_snd))
  exact ((continuous_const.sub ht).smul hv).add (ht.smul hn)

/-- At time zero, every original vertex is unchanged.
See Cairns p. 801 and M76 derivation 18. -/
@[simp] theorem RadialEmbedding.interpolate_zero (v : A.RadialEmbedding E) :
    v.interpolate 0 = v := by
  apply Subtype.ext
  funext i
  change (1 - (0 : ℝ)) • v.val i + (0 : ℝ) • NormedSpace.normalize (v.val i) = v.val i
  simp

/-- At time one, all vertices have been normalized.
See Cairns p. 801 and M76 derivation 18. -/
@[simp] theorem RadialEmbedding.interpolate_one (v : A.RadialEmbedding E) :
    v.interpolate 1 = v.normalized := by
  apply Subtype.ext
  funext i
  change (1 - (1 : ℝ)) • v.val i + (1 : ℝ) • NormedSpace.normalize (v.val i) =
    NormedSpace.normalize (v.val i)
  simp

/-- The entire deformation fixes the unit-vertex subspace.
See Cairns Lemma 5.3 and M76 derivation 18. -/
theorem RadialEmbedding.interpolate_eq_self (v : A.RadialEmbedding E)
    (hv : ∀ i, ‖v.val i‖ = 1) (t : I) : v.interpolate t = v := by
  apply Subtype.ext
  funext i
  change (1 - (t : ℝ)) • v.val i + (t : ℝ) • NormedSpace.normalize (v.val i) = v.val i
  rw [normalize_eq_self_of_norm_eq_one (hv i), ← add_smul]
  simp

/-- The radial normalization as an actual homotopy of vertex spaces.
See Cairns Lemma 5.3 and M76 derivation 18. -/
noncomputable def radialNormalizationHomotopy (A : AbstractSimplicialComplex ι)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.Homotopy (ContinuousMap.id (A.RadialEmbedding E))
      ⟨RadialEmbedding.normalized, RadialEmbedding.continuous_normalized⟩ where
  toFun tv := tv.2.interpolate tv.1
  continuous_toFun := RadialEmbedding.continuous_interpolate
  map_zero_left v := v.interpolate_zero
  map_one_left v := v.interpolate_one

/-- The unit-vertex subspace, with its inherited vertex topology.
See Cairns' normalized mapping space on p. 801 and M76 derivation 18. -/
abbrev UnitRadialEmbedding (A : AbstractSimplicialComplex ι) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  {v : A.RadialEmbedding E // ∀ i, ‖v.val i‖ = 1}

/-- The full radial embedding space and its unit-vertex subspace are
homotopy equivalent via normalization and inclusion. This precedes the
coordinate-change quotient in Cairns Lemma 5.3; see M76 derivation 18. -/
noncomputable def radialNormalizationHomotopyEquiv (A : AbstractSimplicialComplex ι)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContinuousMap.HomotopyEquiv (A.RadialEmbedding E) (A.UnitRadialEmbedding E) where
  toFun := ⟨fun v => ⟨v.normalized, v.norm_normalized⟩,
    RadialEmbedding.continuous_normalized.subtype_mk _⟩
  invFun := ⟨Subtype.val, continuous_subtype_val⟩
  left_inv := ⟨(radialNormalizationHomotopy A E).symm⟩
  right_inv := by
    have heq : (⟨fun v : A.RadialEmbedding E => ⟨v.normalized, v.norm_normalized⟩,
        RadialEmbedding.continuous_normalized.subtype_mk _⟩ :
          C(A.RadialEmbedding E, A.UnitRadialEmbedding E)).comp
        ⟨Subtype.val, continuous_subtype_val⟩ = ContinuousMap.id (A.UnitRadialEmbedding E) := by
      apply ContinuousMap.ext
      intro v
      exact Subtype.ext (v.val.normalized_eq_self v.property)
    rw [heq]

/-- Contractibility transfers exactly between a radial vertex space
and its unit-vertex subspace. See Cairns pp. 801, 807 and M76 derivation 18. -/
theorem contractible_radialEmbedding_iff (A : AbstractSimplicialComplex ι)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ContractibleSpace (A.RadialEmbedding E) ↔ ContractibleSpace (A.UnitRadialEmbedding E) :=
  (radialNormalizationHomotopyEquiv A E).contractibleSpace_iff

end AbstractSimplicialComplex

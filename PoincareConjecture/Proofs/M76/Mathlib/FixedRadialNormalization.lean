import PoincareConjecture.Proofs.M76.Mathlib.RadialEmbeddingNormalization










set_option autoImplicit false

open Set NormedSpace
open scoped unitInterval

namespace AbstractSimplicialComplex

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



abbrev FixedRadialEmbedding (A : AbstractSimplicialComplex ι) (s : Set ι) (w : ι → E) :=
  {v : A.RadialEmbedding E // EqOn v.val w s}



abbrev FixedUnitRadialEmbedding (A : AbstractSimplicialComplex ι) (s : Set ι) (w : ι → E) :=
  {v : A.UnitRadialEmbedding E // EqOn v.val.val w s}

variable {A : AbstractSimplicialComplex ι} {s : Set ι} {w : ι → E}



noncomputable def FixedRadialEmbedding.normalized (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (v : A.FixedRadialEmbedding s w) : A.FixedUnitRadialEmbedding s w :=
  ⟨⟨v.val.normalized, v.val.norm_normalized⟩, by
    intro i hi
    change NormedSpace.normalize (v.val.val i) = w i
    rw [v.property hi, normalize_eq_self_of_norm_eq_one (hw i hi)]⟩



def FixedUnitRadialEmbedding.toFixedRadial (v : A.FixedUnitRadialEmbedding s w) :
    A.FixedRadialEmbedding s w := ⟨v.val.val, v.property⟩



theorem FixedRadialEmbedding.continuous_normalized (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Continuous (FixedRadialEmbedding.normalized hw :
      A.FixedRadialEmbedding s w → A.FixedUnitRadialEmbedding s w) :=
  ((RadialEmbedding.continuous_normalized.comp continuous_subtype_val).subtype_mk _).subtype_mk _



theorem FixedUnitRadialEmbedding.continuous_toFixedRadial :
    Continuous (FixedUnitRadialEmbedding.toFixedRadial :
      A.FixedUnitRadialEmbedding s w → A.FixedRadialEmbedding s w) :=
  (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _



noncomputable def FixedRadialEmbedding.interpolate (hw : ∀ i ∈ s, ‖w i‖ = 1)
    (t : I) (v : A.FixedRadialEmbedding s w) : A.FixedRadialEmbedding s w :=
  ⟨v.val.interpolate t, by
    intro i hi
    change (1 - (t : ℝ)) • v.val.val i + (t : ℝ) • NormedSpace.normalize (v.val.val i) = w i
    rw [v.property hi, normalize_eq_self_of_norm_eq_one (hw i hi), ← add_smul]
    simp⟩



theorem FixedRadialEmbedding.continuous_interpolate (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    Continuous (fun tv : I × A.FixedRadialEmbedding s w => tv.2.interpolate hw tv.1) :=
  (RadialEmbedding.continuous_interpolate.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _




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




theorem contractible_fixedRadialEmbedding_iff (A : AbstractSimplicialComplex ι)
    (s : Set ι) (w : ι → E) (hw : ∀ i ∈ s, ‖w i‖ = 1) :
    ContractibleSpace (A.FixedRadialEmbedding s w) ↔
      ContractibleSpace (A.FixedUnitRadialEmbedding s w) :=
  (fixedRadialNormalizationHomotopyEquiv A s w hw).contractibleSpace_iff

end AbstractSimplicialComplex

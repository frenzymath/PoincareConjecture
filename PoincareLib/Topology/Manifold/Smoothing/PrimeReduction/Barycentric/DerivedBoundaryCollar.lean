import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Collars.PositiveCollarStrips
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.BarycentricNeighborhoodCarrier
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedSubcomplexCarriers

/-!
# Relative openness of the actual derived boundary product

The derived neighborhood supplies an open part of the range in the
original complex. Compactness then gives whole positive open strips
inside any prescribed base neighborhood. See PrimeReduction017.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : SimplicialComplex ℝ E} [Fintype K.faces] [Finite L.faces]

local notation "I" => Icc (0 : ℝ) 1

/-- The same actual compact boundary product has uniformly small
whole strips open in the original complex, including its complete
zero section. No ambient interior is used. See017, sections1--2. -/
theorem exists_small_relative_boundary_product (hLK : L ≤ K)
    (C : (L.space ×ˢ I : Set (E × ℝ)) ≃ₜ (K.barycentricNeighborhood L).space)
    (hzero : ∀ (x : E) (hx : x ∈ L.space),
      (C ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x)
    {U : Set K.space} (hU : IsOpen U)
    (hLU : (Subtype.val : K.space → E) ⁻¹' L.space ⊆ U) :
    ∃ f : L.space × I → K.space,
      (∀ z, (f z : E) = C ⟨((z.1 : E), (z.2 : ℝ)), ⟨z.1.property, z.2.property⟩⟩) ∧
      Topology.IsEmbedding f ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      (∀ (x : L.space) (t : I), (t : ℝ) ≤ δ → f (x, t) ∈ U) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsOpen (f '' {z : L.space × I | (z.2 : ℝ) < ε}) := by
  have hNK : (K.barycentricNeighborhood L).space ⊆ K.space :=
    (space_subset_of_le (K.barycentricNeighborhood_le L)).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  let e := (Homeomorph.Set.prod L.space I).symm
  let f : L.space × I → K.space := Set.inclusion hNK ∘ C ∘ e
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.inclusion hNK).comp (C.isEmbedding.comp e.isEmbedding)
  obtain ⟨O, hO, hLO, hON⟩ := K.exists_open_barycentricNeighborhood hLK
  let W : Set K.space := (Subtype.val : K.space → E) ⁻¹' O ∩ U
  have hW : IsOpen W := (hO.preimage continuous_subtype_val).inter hU
  have hbase (x : L.space) : f (x, ⟨0, le_rfl, zero_le_one⟩) ∈ W := by
    have heq : (f (x, ⟨0, le_rfl, zero_le_one⟩) : E) = x := hzero x x.property
    have hL : (f (x, ⟨0, le_rfl, zero_le_one⟩) : E) ∈ L.space := heq.symm ▸ x.property
    exact ⟨hLO hL, hLU hL⟩
  have hWrange : W ⊆ range f := by
    intro y hy
    have hyN := hON ⟨hy.1, y.property⟩
    obtain ⟨x, hx⟩ := C.surjective ⟨y, hyN⟩
    refine ⟨e.symm x, ?_⟩
    change Set.inclusion hNK (C (e (e.symm x))) = y
    rw [e.apply_symm_apply, hx]
  let : CompactSpace L.space :=
    isCompact_iff_compactSpace.mp (L.isCompact_space_of_finite (Set.toFinite L.faces))
  obtain ⟨δ, hδ, hδsmall, hstrip, hopen⟩ :=
    hf.exists_positive_collar_strips hW hbase hWrange
  exact ⟨f, fun _ => rfl, hf, δ, hδ, hδsmall,
    fun x t ht => (hstrip x t ht).2, hopen⟩

end Geometry.SimplicialComplex

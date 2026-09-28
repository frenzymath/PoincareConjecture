import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.TwoSidedCollarStrips
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricNeighborhoodCarrier
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers










set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K N : SimplicialComplex ℝ E} [Fintype K.faces] [Finite N.faces]

local notation "J" => Icc (-1 : ℝ) 1

theorem exists_small_relative_sphere_product (hNK : N ≤ K)
    (C : (N.space ×ˢ J : Set (E × ℝ)) ≃ₜ (K.barycentricNeighborhood N).space)
    (hzero : ∀ (x : E) (hx : x ∈ N.space),
      (C ⟨(x, 0), ⟨hx, by norm_num⟩⟩ : E) = x)
    {U : Set K.space} (hU : IsOpen U)
    (hNU : (Subtype.val : K.space → E) ⁻¹' N.space ⊆ U) :
    ∃ f : N.space × J → K.space,
      (∀ z, (f z : E) = C ⟨((z.1 : E), (z.2 : ℝ)), ⟨z.1.property, z.2.property⟩⟩) ∧
      Topology.IsEmbedding f ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      (∀ (x : N.space) (t : J), |(t : ℝ)| ≤ δ → f (x, t) ∈ U) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
        IsOpen (f '' {z : N.space × J | |(z.2 : ℝ)| < ε}) := by
  have hDK : (K.barycentricNeighborhood N).space ⊆ K.space :=
    (space_subset_of_le (K.barycentricNeighborhood_le N)).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  let e := (Homeomorph.Set.prod N.space J).symm
  let f : N.space × J → K.space := Set.inclusion hDK ∘ C ∘ e
  have hf : Topology.IsEmbedding f :=
    (Topology.IsEmbedding.inclusion hDK).comp (C.isEmbedding.comp e.isEmbedding)
  obtain ⟨O, hO, hNO, hOD⟩ := K.exists_open_barycentricNeighborhood hNK
  let W : Set K.space := (Subtype.val : K.space → E) ⁻¹' O ∩ U
  have hW : IsOpen W := (hO.preimage continuous_subtype_val).inter hU
  have hbase (x : N.space) : f (x, ⟨0, by norm_num⟩) ∈ W := by
    have heq : (f (x, ⟨0, by norm_num⟩) : E) = x := hzero x x.property
    have hN : (f (x, ⟨0, by norm_num⟩) : E) ∈ N.space := heq.symm ▸ x.property
    exact ⟨hNO hN, hNU hN⟩
  have hWrange : W ⊆ range f := by
    intro y hy
    have hyD := hOD ⟨hy.1, y.property⟩
    obtain ⟨x, hx⟩ := C.surjective ⟨y, hyD⟩
    refine ⟨e.symm x, ?_⟩
    change Set.inclusion hDK (C (e (e.symm x))) = y
    rw [e.apply_symm_apply, hx]
  let : CompactSpace N.space :=
    isCompact_iff_compactSpace.mp (N.isCompact_space_of_finite (Set.toFinite N.faces))
  obtain ⟨δ, hδ, hδsmall, hstrip, hopen⟩ :=
    hf.exists_two_sided_collar_strips hW hbase hWrange
  exact ⟨f, fun _ => rfl, hf, δ, hδ, hδsmall,
    fun x t ht => (hstrip x t ht).2, hopen⟩

end Geometry.SimplicialComplex

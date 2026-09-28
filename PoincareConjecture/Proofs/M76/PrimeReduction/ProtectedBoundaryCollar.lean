import PoincareConjecture.Proofs.M76.PrimeReduction.ProtectedBoundaryProduct
import PoincareConjecture.Proofs.M76.PrimeReduction.DerivedBoundaryCollar
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

open Classical in

theorem exists_protected_small_boundary_collar
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R D U : Set X}
    (hR : IsCompact R) (he : PLDomain e R) (hDR : D ⊆ R)
    (b : ChartwisePLBall e D (frontier D)) (hU : IsOpen U) (hBU : frontier R ⊆ U) :
    ∃ (s : Finset R) (L : SimplicialComplex ℝ (s → ℝ × V3))
      (HB : L.space ≃ₜ frontier R) (c : (s → ℝ × V3) × ℝ → X),
      L.faces.Finite ∧ PolyhedralPLInCharts e c (L.space ×ˢ I) ∧
      Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set ((s → ℝ × V3) × ℝ)) => c z) ∧
      MapsTo c (L.space ×ˢ I) R ∧
      (∀ x : L.space, c ((x : s → ℝ × V3), 0) = HB x) ∧
      (∀ z : (L.space ×ˢ I : Set ((s → ℝ × V3) × ℝ)),
        c z ∈ frontier R ↔ (z : (s → ℝ × V3) × ℝ).2 = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ MapsTo c (L.space ×ˢ Icc 0 δ) U ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ →
          IsOpen ((Subtype.val : R → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 ε))) := by
  classical
  obtain ⟨s, F, K, A, H, g, HB, hK, hL, C, _, _, hA, _, hBs, _, _, hHF,
    _, hg, hgPL, hHB, hC, hC0, hCb⟩ := exists_protected_boundary_product hR he hDR b
  let : Fintype K.faces := hK.fintype
  let : Fintype (A 0).faces := hL.fintype
  let E := s → ℝ × V3
  let L := A 0
  have hNK : (K.barycentricNeighborhood L).space ⊆ K.space :=
    (SimplicialComplex.space_subset_of_le (K.barycentricNeighborhood_le L)).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hfront (z : K.space) : (H.symm z : X) ∈ frontier R ↔ (z : E) ∈ L.space := by
    constructor
    · intro hz
      apply hBs.symm.subset
      have hval := hHF (H.symm z)
      rw [H.apply_symm_apply] at hval
      exact ⟨H.symm z, hz, hval.symm⟩
    · intro hz
      rw [← hg z, ← hHB ⟨z, hz⟩]
      exact (HB ⟨z, hz⟩).property
  let UK : Set K.space := (fun z : K.space => (H.symm z : X)) ⁻¹' U
  have hUK : IsOpen UK := hU.preimage (continuous_subtype_val.comp H.symm.continuous)
  have hLUK : (Subtype.val : K.space → E) ⁻¹' L.space ⊆ UK :=
    fun z hz => hBU ((hfront z).mpr hz)
  obtain ⟨f, hfval, hf, δ, hδ, hδsmall, hthin, hopen⟩ :=
    SimplicialComplex.exists_small_relative_boundary_product (hA 0).1 C hC0 hUK hLUK
  obtain ⟨cE, hcE, hcval⟩ := hC
  let c : E × ℝ → X := fun z => (g (cE z) : X)
  have hcF (z : L.space × I) : c ((z.1 : E), (z.2 : ℝ)) = (H.symm (f z) : X) := by
    change (g (cE ((z.1 : E), (z.2 : ℝ))) : X) = _
    rw [← hcval ⟨((z.1 : E), (z.2 : ℝ)), ⟨z.1.property, z.2.property⟩⟩, ← hfval z]
    exact hg (f z)
  have hcPL : PolyhedralPLInCharts e c (L.space ×ˢ I) := by
    obtain ⟨J, hJ, hJs, hJa⟩ := hcE
    have hcJ : FinitePiecewiseAffineOn cE J.space := ⟨J, hJ, rfl, hJa⟩
    have hmap : MapsTo cE J.space K.space := by
      intro z hz
      rw [← hcval ⟨z, hJs.subset hz⟩]
      exact hNK (C ⟨z, hJs.subset hz⟩).property
    have h := hgPL.comp_finitePiecewiseAffineOn J hJ hcJ hmap
    exact hJs ▸ h
  have hemb : Topology.IsEmbedding (fun z : L.space × I => c ((z.1 : E), (z.2 : ℝ))) := by
    have h := Topology.IsEmbedding.subtypeVal.comp (H.symm.isEmbedding.comp hf)
    convert h using 1
    funext z
    exact hcF z
  have hemb' : Topology.IsEmbedding (fun z : (L.space ×ˢ I : Set (E × ℝ)) => c z) :=
    hemb.comp (Homeomorph.Set.prod L.space I).isEmbedding
  refine ⟨s, L, HB, c, hL, hcPL, hemb', (fun z _ => (g (cE z)).property), ?_, ?_,
    δ, hδ, hδsmall, ?_, ?_⟩
  · intro x
    change (g (cE ((x : E), 0)) : X) = _
    rw [← hcval ⟨((x : E), 0), ⟨x.property, le_rfl, zero_le_one⟩⟩, hC0 x x.property]
    exact (hHB x).symm
  · intro z
    have h := hcF ((Homeomorph.Set.prod L.space I) z)
    change c z = _ at h
    rw [h, hfront, hfval]
    exact hCb z
  · intro z hz
    have ht : z.2 ∈ I := ⟨hz.2.1, by linarith [hz.2.2]⟩
    rw [hcF (⟨z.1, hz.1⟩, ⟨z.2, ht⟩)]
    exact hthin ⟨z.1, hz.1⟩ ⟨z.2, ht⟩ hz.2.2
  · intro ε hε hεδ
    have heq : H ⁻¹' (f '' {z : L.space × I | (z.2 : ℝ) < ε}) =
        (Subtype.val : R → X) ⁻¹' (c '' (L.space ×ˢ Ico 0 ε)) := by
      ext y
      constructor
      · rintro ⟨z, hz, hzy⟩
        refine ⟨((z.1 : E), (z.2 : ℝ)), ⟨z.1.property, z.2.property.1, hz⟩, ?_⟩
        rw [hcF z, hzy, H.symm_apply_apply]
      · rintro ⟨z, hz, hzy⟩
        have ht : z.2 ∈ I := ⟨hz.2.1, by linarith [hz.2.2]⟩
        let w : L.space × I := (⟨z.1, hz.1⟩, ⟨z.2, ht⟩)
        have hval : (H.symm (f w) : X) = y := (hcF w).symm.trans hzy
        have hsub : H.symm (f w) = y := Subtype.ext hval
        refine ⟨w, hz.2.2, ?_⟩
        exact H.symm.injective (hsub.trans (H.symm_apply_apply y).symm)
    rw [← heq]
    exact (hopen ε hε hεδ).preimage H.continuous

end PoincareConjecture.M76

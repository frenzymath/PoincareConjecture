import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.OriginalSphereCompactBicollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Barycentric.DerivedSphereCollar
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PolyhedralPLComposition










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "J" => Icc (-1 : ℝ) 1





theorem ChartwisePLSphere.exists_original_small_bicollar_with_model
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ (t : Finset R) (F : X → (t → ℝ × V3))
      (N : SimplicialComplex ℝ (t → ℝ × V3))
      (HB : N.space ≃ₜ S) (c : (t → ℝ × V3) × ℝ → X),
      Continuous F ∧
      (∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) ∧
      InjOn F R ∧ N.space = F '' S ∧
      N.faces.Finite ∧ PolyhedralPLInCharts e c (N.space ×ˢ J) ∧
      Topology.IsEmbedding (fun z : (N.space ×ˢ J : Set ((t → ℝ × V3) × ℝ)) => c z) ∧
      MapsTo c (N.space ×ˢ J) R ∧
      (∀ x : N.space, c ((x : t → ℝ × V3), 0) = HB x) ∧
      (∀ z : (N.space ×ˢ J : Set ((t → ℝ × V3) × ℝ)),
        c z ∈ S ↔ (z : (t → ℝ × V3) × ℝ).2 = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
        MapsTo c (N.space ×ˢ Icc (-δ) δ) (U ∩ interior R) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ → IsOpen (c '' (N.space ×ˢ Ioo (-ε) ε)) := by
  classical
  obtain ⟨t, F, K, L, N, T, P, M, H, g, W, Rp, Rn, B, hK, hT, hP, hM, hN,
    FP, FM, EP, EM, VP, VM, CP, CM, C, hC, _, _, _, _, hC0, hCb,
    _, _, _, _, _, hdata⟩ := s.exists_original_compact_bicollar hR he hSR
  let : Fintype K.faces := hK.fintype
  let : Fintype N.faces := hN.fintype
  obtain ⟨hFc, hFcharts, _, hTK, hNT, _, _, _, _, _, _, _, _, _, _, _, hNs,
    hHF, _, hg, hgPL, _⟩ := hdata
  have hFi : InjOn F R := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hHF ⟨x, hx⟩).trans (hxy.trans (hHF ⟨y, hy⟩).symm))))
  let E := t → ℝ × V3
  have hNK : N ≤ K := fun _ ha => hTK (hNT ha)
  have hNsK : N.space ⊆ K.space := SimplicialComplex.space_subset_of_le hNK
  have hDK : (K.barycentricNeighborhood N).space ⊆ K.space :=
    (SimplicialComplex.space_subset_of_le (K.barycentricNeighborhood_le N)).trans
      K.barycentricSubdivision_isSubdivision.space_eq.subset
  have hsphere (z : K.space) : (H.symm z : X) ∈ S ↔ (z : E) ∈ N.space := by
    constructor
    · intro hz
      apply hNs.symm.subset
      have hval := hHF (H.symm z)
      rw [H.apply_symm_apply] at hval
      exact ⟨H.symm z, hz, hval.symm⟩
    · intro hz
      obtain ⟨x, hx, hFx⟩ := hNs.subset hz
      have hHx : H ⟨x, interior_subset (hSR hx)⟩ = z :=
        Subtype.ext ((hHF ⟨x, interior_subset (hSR hx)⟩).trans hFx)
      have hback := congrArg H.symm hHx
      rw [H.symm_apply_apply] at hback
      have hval := congrArg Subtype.val hback
      exact hval ▸ hx
  let HB : N.space ≃ₜ S := {
    toFun := fun x => ⟨H.symm ⟨x, hNsK x.property⟩,
      (hsphere ⟨x, hNsK x.property⟩).mpr x.property⟩
    invFun := fun x => ⟨F x, hNs.symm.subset ⟨x, x.property, rfl⟩⟩
    left_inv := by
      intro x
      apply Subtype.ext
      exact (hHF (H.symm ⟨x, hNsK x.property⟩)).symm.trans
        (congrArg Subtype.val (H.apply_symm_apply ⟨x, hNsK x.property⟩))
    right_inv := by
      intro x
      apply Subtype.ext
      have hfx : (⟨F x, hNsK (hNs.symm.subset ⟨x, x.property, rfl⟩)⟩ : K.space) =
          H ⟨x, interior_subset (hSR x.property)⟩ :=
        Subtype.ext (hHF ⟨x, interior_subset (hSR x.property)⟩).symm
      change (H.symm ⟨F x, _⟩ : X) = x
      rw [hfx, H.symm_apply_apply]
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (H.symm.continuous.comp (continuous_inclusion hNsK))
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact hFc.comp continuous_subtype_val }
  have hHB (x : N.space) : (HB x : X) = (g x : X) :=
    (hg ⟨x, hNsK x.property⟩).symm
  let UK : Set K.space := (fun z : K.space => (H.symm z : X)) ⁻¹' (U ∩ interior R)
  have hUK : IsOpen UK := (hU.inter isOpen_interior).preimage
    (continuous_subtype_val.comp H.symm.continuous)
  have hNUK : (Subtype.val : K.space → E) ⁻¹' N.space ⊆ UK := by
    intro z hz
    have hzS := (hsphere z).mpr hz
    exact ⟨hSU hzS, hSR hzS⟩
  obtain ⟨f, hfval, hf, δ, hδ, hδsmall, hthin, hopen⟩ :=
    SimplicialComplex.exists_small_relative_sphere_product hNK C hC0 hUK hNUK
  obtain ⟨cE, hcE, hcval⟩ := hC
  let c : E × ℝ → X := fun z => (g (cE z) : X)
  have hcF (z : N.space × J) : c ((z.1 : E), (z.2 : ℝ)) = (H.symm (f z) : X) := by
    change (g (cE ((z.1 : E), (z.2 : ℝ))) : X) = _
    rw [← hcval ⟨((z.1 : E), (z.2 : ℝ)), ⟨z.1.property, z.2.property⟩⟩, ← hfval z]
    exact hg (f z)
  have hcPL : PolyhedralPLInCharts e c (N.space ×ˢ J) := by
    obtain ⟨A, hA, hAs, hAa⟩ := hcE
    have hcA : FinitePiecewiseAffineOn cE A.space := ⟨A, hA, rfl, hAa⟩
    have hmap : MapsTo cE A.space K.space := by
      intro z hz
      rw [← hcval ⟨z, hAs.subset hz⟩]
      exact hDK (C ⟨z, hAs.subset hz⟩).property
    exact hAs ▸ hgPL.comp_finitePiecewiseAffineOn A hA hcA hmap
  have hemb : Topology.IsEmbedding (fun z : N.space × J => c ((z.1 : E), (z.2 : ℝ))) := by
    have h := Topology.IsEmbedding.subtypeVal.comp (H.symm.isEmbedding.comp hf)
    convert h using 1
    funext z
    exact hcF z
  have hemb' : Topology.IsEmbedding (fun z : (N.space ×ˢ J : Set (E × ℝ)) => c z) :=
    hemb.comp (Homeomorph.Set.prod N.space J).isEmbedding
  have hthin' : MapsTo c (N.space ×ˢ Icc (-δ) δ) (U ∩ interior R) := by
    intro z hz
    have ht : z.2 ∈ J := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
    rw [hcF (⟨z.1, hz.1⟩, ⟨z.2, ht⟩)]
    exact hthin ⟨z.1, hz.1⟩ ⟨z.2, ht⟩ (abs_le.mpr hz.2)
  refine ⟨t, F, N, HB, c, hFc, hFcharts, hFi, hNs, hN, hcPL, hemb',
    (fun z _ => (g (cE z)).property), ?_, ?_,
    δ, hδ, hδsmall, hthin', ?_⟩
  · intro x
    change (g (cE ((x : E), 0)) : X) = _
    rw [← hcval ⟨((x : E), 0), ⟨x.property, by norm_num⟩⟩, hC0 x x.property]
    exact (hHB x).symm
  · intro z
    have h := hcF ((Homeomorph.Set.prod N.space J) z)
    change c z = _ at h
    rw [h, hsphere, hfval]
    exact hCb z
  · intro ε hε hεδ
    let A := c '' (N.space ×ˢ Ioo (-ε) ε)
    have hAint : A ⊆ interior R := by
      rintro y ⟨z, hz, rfl⟩
      exact (hthin' ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩).2
    have heq : H ⁻¹' (f '' {z : N.space × J | |(z.2 : ℝ)| < ε}) =
        (Subtype.val : R → X) ⁻¹' A := by
      ext y
      constructor
      · rintro ⟨z, hz, hzy⟩
        refine ⟨((z.1 : E), (z.2 : ℝ)), ⟨z.1.property, abs_lt.mp hz⟩, ?_⟩
        rw [hcF z, hzy, H.symm_apply_apply]
      · rintro ⟨z, hz, hzy⟩
        have ht : z.2 ∈ J := ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
        let w : N.space × J := (⟨z.1, hz.1⟩, ⟨z.2, ht⟩)
        have hval : (H.symm (f w) : X) = y := (hcF w).symm.trans hzy
        have hsub : H.symm (f w) = y := Subtype.ext hval
        exact ⟨w, abs_lt.mpr hz.2,
          H.symm.injective (hsub.trans (H.symm_apply_apply y).symm)⟩
    have hrel : IsOpen ((Subtype.val : R → X) ⁻¹' A) := by
      rw [← heq]
      exact (hopen ε hε hεδ).preimage H.continuous
    have hrelint : IsOpen ((Subtype.val : interior R → X) ⁻¹' A) :=
      hrel.preimage (continuous_inclusion (interior_subset (s := R)))
    have hAopen : IsOpen (interior R ∩ A) := isOpen_interior.inter_preimage_val_iff.mp hrelint
    simpa only [inter_eq_right.mpr hAint] using hAopen





theorem ChartwisePLSphere.exists_original_small_bicollar
    {X ι : Type*} [MetricSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R S U : Set X}
    (s : ChartwisePLSphere e S) (hR : IsCompact R) (he : PLDomain e R)
    (hSR : S ⊆ interior R) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ (t : Finset R) (N : SimplicialComplex ℝ (t → ℝ × V3))
      (HB : N.space ≃ₜ S) (c : (t → ℝ × V3) × ℝ → X),
      N.faces.Finite ∧ PolyhedralPLInCharts e c (N.space ×ˢ J) ∧
      Topology.IsEmbedding (fun z : (N.space ×ˢ J : Set ((t → ℝ × V3) × ℝ)) => c z) ∧
      MapsTo c (N.space ×ˢ J) R ∧
      (∀ x : N.space, c ((x : t → ℝ × V3), 0) = HB x) ∧
      (∀ z : (N.space ×ˢ J : Set ((t → ℝ × V3) × ℝ)),
        c z ∈ S ↔ (z : (t → ℝ × V3) × ℝ).2 = 0) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
        MapsTo c (N.space ×ˢ Icc (-δ) δ) (U ∩ interior R) ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ δ → IsOpen (c '' (N.space ×ˢ Ioo (-ε) ε)) := by
  obtain ⟨t, F, N, HB, c, _, _, _, _, hrest⟩ :=
    s.exists_original_small_bicollar_with_model hR he hSR hU hSU
  exact ⟨t, N, HB, c, hrest⟩

end PoincareConjecture.M76

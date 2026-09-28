import PoincareConjecture.Proofs.M76.Mathlib.ParametricSmoothCore
import PoincareConjecture.Proofs.M76.Mathlib.NormalizedFieldGerms
import PoincareConjecture.Proofs.M76.Mathlib.CompactLeafGluing

set_option autoImplicit false

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace ContinuousAffineMap

variable {X Y E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_smooth_parametric_leafAttachment (a : F →ᴬ[ℝ] E)
    (b : (X × Y) ≃L[ℝ] F) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse a.contLinear Q0)
    {C : Set X} (hC : IsCompact C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    {P K : Set Y} (hP : IsCompact P) (hK : IsCompact K) (hKP : K ⊆ interior P)
    {G : E → E →L[ℝ] F} {V : Set E} (hV : IsOpen V) (hG : ContDiffOn ℝ ∞ G V)
    (hnorm : ∀ y ∈ V, Function.RightInverse a.contLinear (G y))
    (hleaf : ∀ y ∈ V, ∀ᶠ w in 𝓝 y, w - y ∈ (G y).ker → G w = G y)
    (hboundary : (a ∘ b) '' (frontier C ×ˢ P) ⊆ V) (A : Set E)
    [ContractibleSpace {Q : E →L[ℝ] F // Function.RightInverse a.contLinear Q ∧
      Q.ker.IsSecantTransverse A}]
    (htrans : ∀ z ∈ frontier C ×ˢ P, (G (a (b z))).ker.IsSecantTransverse A) :
    ∃ U : Set E, IsOpen U ∧ (a ∘ b) '' (C ×ˢ K) ⊆ U ∧
      ∃ g : E → E →L[ℝ] F, ContDiffOn ℝ ∞ g U ∧
        (∀ y ∈ U, Function.RightInverse a.contLinear (g y) ∧ (g y).ker.IsSecantTransverse A) ∧
        (∀ y ∈ U, ∀ᶠ w in 𝓝 y, w - y ∈ (g y).ker → g w = g y) ∧
        G =ᶠ[𝓝ˢ ((a ∘ b) '' (frontier C ×ˢ K))] g := by
  let H : X × Y → E →L[ℝ] F := fun z => G (a (b z))
  let D : Set (X × Y) := frontier C ×ˢ P
  let S : Set (X × Y) := frontier C ×ˢ K
  let T : Set (X × Y) := (a ∘ b) ⁻¹' V
  have hKP' : K ⊆ P := hKP.trans interior_subset
  have hSD : S ⊆ D := prod_mono Subset.rfl hKP'
  have hS : IsClosed S := isClosed_frontier.prod hK.isClosed
  have hD : IsClosed D := isClosed_frontier.prod hP.isClosed
  have hab : ContDiff ℝ ∞ (a ∘ b) := a.contDiff.comp b.contDiff
  have hT : IsOpen T := hV.preimage hab.continuous
  have hDT : D ⊆ T := fun z hz => hboundary ⟨z, hz, rfl⟩
  have hH : ContDiffOn ℝ ∞ H T := hG.comp hab.contDiffOn (fun _ hz => hz)
  obtain ⟨f, hfn, hfH⟩ := hH.continuousOn.exists_frame_extension_eventuallyEq hD
    (hT.mem_nhdsSet.mpr hDT) a.contLinear Q0 h0 (fun z hz => hnorm _ hz)
  have hfHS : (f : X × Y → E →L[ℝ] F) =ᶠ[𝓝ˢ S] H :=
    hfH.filter_mono (nhdsSet_mono hSD)
  obtain ⟨O, hO, hSO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp hfHS
  have hTO : T ∩ O ∈ 𝓝ˢ S :=
    Filter.inter_mem (hT.mem_nhdsSet.mpr (hSD.trans hDT)) (hO.mem_nhdsSet.mpr hSO)
  have hfsmooth : ContDiffOn ℝ ∞ (f : X × Y → E →L[ℝ] F) (T ∩ O) :=
    (hH.mono inter_subset_left).congr (fun z hz => hOeq z hz.2)
  have hftrans : ∀ x ∈ frontier C, ∀ p ∈ P, (f (x, p)).ker.IsSecantTransverse A := by
    intro x hx p hp
    rw [hfH.self_of_nhdsSet ⟨hx, hp⟩]
    exact htrans (x, p) ⟨hx, hp⟩
  obtain ⟨k, hk, hkn, hkeq, hkt⟩ :=
    f.continuous.exists_contDiff_frameTransverse_parametric_coreExtension a.contLinear hfn (⊤ : ℕ∞)
      hC hc hi hP hK hKP hS (fun z hz => ⟨hz.1.2, hz.2⟩) hTO hfsmooth A hftrans
  have hkH : k =ᶠ[𝓝ˢ S] H := hkeq.trans hfHS
  let Q : F → E →L[ℝ] F := fun v => k (b.symm v)
  have hQ : ContDiff ℝ ∞ Q := hk.comp b.symm.contDiff
  have hQn (v : F) : Function.RightInverse a.contLinear (Q v) := hkn (b.symm v)
  let C' := b '' (C ×ˢ K)
  let S' := b '' S
  have hC' : IsCompact C' := (hC.prod hK).image b.continuous
  have hS'C' : S' ⊆ C' := image_mono (prod_mono hC.isClosed.frontier_subset Subset.rfl)
  have hV' : V ∈ 𝓝ˢ (a '' S') := by
    apply hV.mem_nhdsSet.mpr
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hboundary ⟨z, hSD hz, rfl⟩
  have hslice : ∀ v ∈ S', (fun u => G (a u)) =ᶠ[𝓝 v] Q := by
    rintro _ ⟨z, hz, rfl⟩
    have hzEq : k =ᶠ[𝓝 z] H := eventually_nhdsSet_iff_forall.mp hkH z hz
    have hbeq : Tendsto b.symm (𝓝 (b z)) (𝓝 z) := by
      simpa only [b.symm_apply_apply] using
        (b.symm.continuous.continuousAt (x := b z)).tendsto
    filter_upwards [hbeq.eventually hzEq] with v hv
    simpa only [Q, H, b.apply_symm_apply] using hv.symm
  let W : Set (E →L[ℝ] F) :=
    {R | (frameNormalize a.contLinear Q0 R).ker.IsSecantTransverse A}
  have hW : IsOpen W := isOpen_frameNormalize_transverse a.contLinear Q0 h0 A
  have hQW : MapsTo Q C' W := by
    rintro _ ⟨z, hz, rfl⟩
    change (frameNormalize a.contLinear Q0 (Q (b z))).ker.IsSecantTransverse A
    rw [frameNormalize_eq_self a.contLinear Q0 _ (hQn (b z))]
    simpa only [Q, b.symm_apply_apply] using hkt z hz
  obtain ⟨U, hU, hCU, g, hg, _, hgm, hgl, hgeq⟩ :=
    a.exists_smooth_affineLeaf_extension_matching hQ hQn hC' hS'C' hW hQW hV'
      hG.continuousOn hleaf hslice
  refine ⟨U, hU, ?_, g, hg, ?_, hgl, ?_⟩
  · simpa only [C', image_image, Function.comp_def] using hCU
  · intro y hy
    obtain ⟨hgn, hgw⟩ := hgm y hy
    refine ⟨hgn, ?_⟩
    change (frameNormalize a.contLinear Q0 (g y)).ker.IsSecantTransverse A at hgw
    rwa [frameNormalize_eq_self a.contLinear Q0 (g y) hgn] at hgw
  · simpa only [S', S, image_image, Function.comp_def] using hgeq

end ContinuousAffineMap

import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Ambient

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev P := E2 × Real

theorem exists_restriction_eq_surface_zero_section
    {f : S2 -> E3} (hf : Topology.IsEmbedding f) (p : S2)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (F : OpenPartialHomeomorph P E3) (hF0 : 0 ∈ F.source) (hFp : F 0 = f p)
    (hFsurface : ∀ x, (x, 0) ∈ F.source -> F (x, 0) = f (e x)) :
    ∃ G : OpenPartialHomeomorph P E3,
      0 ∈ G.source ∧ G.source ⊆ F.source ∧ G.target ⊆ F.target ∧
      (G : P -> E3) = F ∧ (G.symm : E3 -> P) = F.symm ∧
      range f ∩ G.target = G '' (G.source ∩ {z : P | z.2 = 0}) := by
  let A : Set S2 := e.target ∩ e.symm ⁻¹' {x : E2 | (x, 0) ∈ F.source}
  have hA : IsOpen A := e.continuousOn_symm.isOpen_inter_preimage e.open_target
    (F.open_source.preimage (continuous_id.prodMk continuous_const))
  have hpA : p ∈ A := by
    have hep' : e.symm p = 0 := by rw [← hep, e.left_inv he0]
    refine ⟨hep ▸ e.map_source he0, ?_⟩
    change (e.symm p, 0) ∈ F.source
    rw [hep']
    exact hF0
  obtain ⟨O, hO, hOA⟩ := hf.isInducing.isOpen_iff.mp hA
  have hfpO : f p ∈ O := by
    change p ∈ f ⁻¹' O
    rw [hOA]
    exact hpA
  let G := (F.symm.restrOpen O hO).symm
  have hGs : G.source = F.source ∩ F ⁻¹' O := rfl
  have hGt : G.target = F.target ∩ O := rfl
  have hGeq : (G : P -> E3) = F := rfl
  refine ⟨G, ?_, ?_, ?_, hGeq, rfl, ?_⟩
  · rw [hGs]
    exact ⟨hF0, by simpa only [mem_preimage, hFp] using hfpO⟩
  · rw [hGs]
    exact inter_subset_left
  · rw [hGt]
    exact inter_subset_left
  · ext y
    constructor
    · rintro ⟨⟨q, rfl⟩, hy⟩
      have hqA : q ∈ A := by
        rw [← hOA]
        exact (show f q ∈ F.target ∩ O from hy).2
      have hzero : (e.symm q, 0) ∈ F.source := hqA.2
      have heq : F (e.symm q, 0) = f q := by
        rw [hFsurface _ hzero, e.right_inv hqA.1]
      refine ⟨(e.symm q, 0), ⟨?_, rfl⟩, heq⟩
      rw [hGs]
      exact ⟨hzero, by rw [mem_preimage, heq]; exact (show f q ∈ F.target ∩ O from hy).2⟩
    · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
      refine ⟨?_, G.map_source hz⟩
      have hzF : z ∈ F.source := (show z ∈ F.source ∩ F ⁻¹' O from hz).1
      have hz0 : z = (z.1, 0) := Prod.ext rfl hzt
      refine ⟨e z.1, ?_⟩
      rw [hGeq, hz0, hFsurface _ (hz0 ▸ hzF)]

theorem exists_ambient_height_coordinates_exact
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target) :
    ∃ F : OpenPartialHomeomorph P E3,
      0 ∈ F.source ∧ F.source ⊆ e.source ×ˢ univ ∧ F 0 = f p ∧
      ContDiffOn Real ∞ F F.source ∧ ContDiffOn Real ∞ F.symm F.target ∧
      (∀ z ∈ F.source, F z = f (e z.1) + z.2 • (v : E3)) ∧
      range f ∩ F.target = F '' (F.source ∩ {z : P | z.2 = 0}) := by
  obtain ⟨F, hF0, hFs, hFp, hF, hFi, hFeq⟩ :=
    exists_ambient_height_coordinates hf v p hp e he0 hep he hei
  obtain ⟨G, hG0, hGs, hGt, hGeq, hGieq, hsection⟩ :=
    exists_restriction_eq_surface_zero_section hf.isEmbedding p e he0 hep F hF0 hFp
      (fun x hx => by simpa only [zero_smul, add_zero] using hFeq (x, 0) hx)
  refine ⟨G, hG0, hGs.trans hFs, ?_, ?_, ?_, ?_, hsection⟩
  · rw [hGeq, hFp]
  · rw [hGeq]
    exact hF.mono hGs
  · rw [hGieq]
    exact hFi.mono hGt
  · intro z hz
    rw [hGeq]
    exact hFeq z (hGs hz)

theorem exists_ambient_morse_coordinates_exact
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v p : S2)
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun q => inner Real (v : E3) (f q)) p = 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 -> Real)
    (hform : ∀ x ∈ e.source, inner Real (v : E3) (f (e x)) =
      inner Real (v : E3) (f p) + ∑ i : Fin 2, σ i * x i ^ 2) :
    ∃ F : OpenPartialHomeomorph P E3,
      0 ∈ F.source ∧ F.source ⊆ e.source ×ˢ univ ∧ F 0 = f p ∧
      ContDiffOn Real ∞ F F.source ∧ ContDiffOn Real ∞ F.symm F.target ∧
      (∀ z ∈ F.source, F z = f (e z.1) + z.2 • (v : E3)) ∧
      range f ∩ F.target = F '' (F.source ∩ {z : P | z.2 = 0}) ∧
      ∀ z ∈ F.source, inner Real (v : E3) (F z) =
        inner Real (v : E3) (f p) + (∑ i : Fin 2, σ i * z.1 i ^ 2) + z.2 := by
  obtain ⟨F, hF0, hFs, hFp, hF, hFi, hFeq, hsection⟩ :=
    exists_ambient_height_coordinates_exact hf v p hp e he0 hep he hei
  refine ⟨F, hF0, hFs, hFp, hF, hFi, hFeq, hsection, ?_⟩
  intro z hz
  rw [hFeq z hz, inner_add_right, inner_smul_right, hform z.1 (hFs hz).1]
  simp

end Poincare.Manifold.Schoenflies

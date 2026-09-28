import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.CenteredStrips
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.PhysicalModelChart



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}




theorem exists_terminal_model_slab_transport
    (d : TerminalSaddleGeometry M P p e) (s : ActualStripData d)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hsize : 2 * d.r < Real.sqrt d.scale * d.matchingRadius)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    (Nreg : Set E2) (hNreg : IsOpen Nreg)
    (hQNreg : Saddle.toE2 '' (((d.flatten ∘ g) '' (e '' closedSquare d.r)) ∩
      {y : E3 | y 2 = inner Real (M.v : E3) (g p)}) ⊆ Nreg) :
    let c := inner Real (M.v : E3) (g p)
    ∃ (δ : Real) (C K O N : Set E2) (V : Set E3),
      0 < δ ∧ δ ≤ d.delta ∧ IsCompact C ∧ C ⊆ Nreg ∧ IsCompact K ∧ IsOpen O ∧
      C ⊆ O ∧ Disjoint K O ∧ IsOpen N ∧ C ⊆ N ∧ N ⊆ Nreg ∧ IsOpen V ∧
      (d.flatten ∘ g) '' (e '' closedSquare d.r) ⊆ V ∧
      (∀ t ∈ Icc (-δ) δ,
        {x : E2 | Saddle.toE3 x (c + t) ∈
          (d.flatten ∘ g) '' (e '' closedSquare d.r)} ⊆ C) ∧
      (∀ t ∈ Icc (-δ) δ, ∀ x, Saddle.toE3 x (c + t) ∈ V → x ∈ C) ∧
      (∀ t ∈ Icc (-δ) δ, d.A (c + t) \ C = d.A c \ C) ∧
      (∀ t ∈ Icc (-δ) δ, d.A (c + t) ∩ N = d.B (c + t) ∩ N) ∧
      ∃ Psi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Psi 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Psi z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Psi z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Psi t x = x) ∧
        (∀ t x, x ∈ O → Psi t x = x) ∧
        ∀ t ∈ Icc (-δ) δ, Psi t '' (d.B c \ C) = d.B (c + t) \ C := by
  classical
  let c := inner Real (M.v : E3) (g p)
  let J := terminalCenteredFrame d
  let D := terminalCenteredFlattening d
  let G := terminalCenteredModel d
  let gc : S2 → E3 := fun q => J (g q)
  let h : S2 → Real := fun q => inner Real (M.v : E3) (d.filledModel q)
  obtain ⟨E, hEsquare, hE0, hEp, hE, hEi, hEsource, hEmatch, hEform⟩ :=
    exists_physical_model_morse_chart d hsize hform
  obtain ⟨hh, hcenter, _, hunique, hconnected⟩ :=
    terminal_physical_model_central_level_facts d hform
  change h (d.modelChart 0) = c at hcenter
  have hEform' (x : E2) (hx : x ∈ E.source) :
      h (E x) = h (d.modelChart 0) - x 0 ^ 2 + x 1 ^ 2 := by
    rw [hcenter]
    exact hEform x hx
  have hGheight (q : S2) : G q 2 = 1 * (h q - h (d.modelChart 0)) := by
    change terminalCenteredFrame d (d.filledModel q) 2 = _
    rw [terminalCenteredFrame_height, one_mul, hcenter]
  obtain ⟨U, hU, hQUraw, hcommonraw⟩ :=
    Saddle.Nested.exists_common_neighborhood_of_matching hg.contMDiff.continuous
      hg.isEmbedding.injective
      d.filledModel J d.scale_pos d.r_pos.le hsize d.matching_source
      d.matching_actual_source d.matching
  have hgr : range gc = J '' range g := by
    simp only [gc, ← Function.comp_def, range_comp]
  have hcommon : (G '' sphere (0 : E3) 1) ∩ U = range gc ∩ U := by
    rw [hgr]
    exact hcommonraw.symm
  have hQU : gc '' (e '' closedSquare d.r) ⊆ U := by
    simpa only [gc, image_image, Function.comp_apply] using hQUraw
  have hQN : Saddle.toE2 '' (((D ∘ gc) '' (e '' closedSquare d.r)) ∩
      {y : E3 | y 2 = 0}) ⊆ Nreg := by
    rintro _ ⟨_, ⟨⟨q, hq, rfl⟩, hqheight⟩, rfl⟩
    have hqheight' : d.flatten (g q) 2 = c := by
      change terminalCenteredFlattening d (terminalCenteredFrame d (g q)) 2 = 0 at hqheight
      rw [terminalCenteredFlattening_apply_frame, terminalCenteredFrame_height] at hqheight
      change d.frame (d.D (g q)) 2 = c
      rw [d.frame_height]
      exact sub_eq_zero.mp hqheight
    have hproj : Saddle.toE2 ((D ∘ gc) q) = Saddle.toE2 (d.flatten (g q)) := by
      change Saddle.toE2 (terminalCenteredFlattening d (terminalCenteredFrame d (g q))) = _
      rw [terminalCenteredFlattening_apply_frame, terminalCenteredFrame_projection]
      rfl
    rw [hproj]
    exact hQNreg ⟨d.flatten (g q), ⟨⟨q, hq, rfl⟩, hqheight'⟩, rfl⟩
  have hmatch (x : E2) (hx : x ∈ closedSquare d.r) :
      G (E x) = gc (e (Real.sqrt 1 • x)) := by
    change J (d.filledModel (E x)) = J (g (e (Real.sqrt 1 • x)))
    simpa only [Real.sqrt_one, one_smul] using congrArg J (hEmatch x (hEsquare hx))
  obtain ⟨δ, C, K, O, N, V, hδ, hδdelta, hC, hCNreg, hK, hO, hCO, hKO,
      hN, hCN, hNNreg, hV, hQV, hclosedC, hVC, hsource, hcommonN,
      Psi, hPsi0, hPsi, hPsiinv, hfix, hfixO, hmove⟩ :=
    Saddle.Nested.exists_model_slab_transport_of_central_level G D
      (terminalCenteredFlattening_height d)
      (terminalCenteredFlattening_zero d s.fixed_critical_plane)
      hh hunique hconnected E hE0 hEp hE hEi hEform' d.r_pos (by norm_num : (0 : Real) < 1)
      hEsquare hGheight gc (J.continuous.comp hg.contMDiff.continuous)
      (J.injective.comp hg.isEmbedding.injective) e hmatch
      hU hcommon (by simpa only [Real.sqrt_one, one_mul] using hQU)
      d.strips d.a s.centralLeft s.centralRight d.b s.central_chain s.contactLabels
      (by simpa only [Real.sqrt_one, one_mul] using s.endpoint_labels)
      d.delta_pos
      (fun i z hz => terminal_strip_closed_rectangle d s i
        ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩)
      (fun i z hz => terminal_centered_strip_height d s i z
        (terminal_strip_closed_rectangle d s i
          ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩))
      (fun i x hx t ht => terminal_centered_strip_flattening d s i x hx t
        (Ioo_subset_Icc_self ht))
      (terminalActualTrace d)
      (fun t ht => by
        simpa only [Real.sqrt_one, one_mul, D, gc, J, Function.comp_def] using
          terminal_centered_actual_level_eq_open_patch_union_trace d s t ht)
      Nreg hNreg (by simpa only [Real.sqrt_one, one_mul] using hQN)
  simp only [Real.sqrt_one, one_mul] at hQV hclosedC
  have hAfiber (t : Real) : {x : E2 | Saddle.toE3 x t ∈ range (D ∘ gc)} = d.A (c + t) :=
    terminalCenteredFlattening_actual_fiber d t
  have hBfiber (t : Real) :
      {x : E2 | Saddle.toE3 x t ∈ (G.trans D) '' sphere (0 : E3) 1} = d.B (c + t) :=
    terminalCenteredFlattening_model_fiber d t
  have hsource' (t : Real) (ht : t ∈ Icc (-δ) δ) : d.A (c + t) \ C = d.A c \ C := by
    have H := hsource t ht
    change {x : E2 | Saddle.toE3 x t ∈ range (D ∘ gc)} \ C =
      {x : E2 | Saddle.toE3 x 0 ∈ range (D ∘ gc)} \ C at H
    simpa only [hAfiber, add_zero] using H
  have hcommonN' (t : Real) (ht : t ∈ Icc (-δ) δ) :
      d.A (c + t) ∩ N = d.B (c + t) ∩ N := by
    have H := hcommonN t ht
    change {x : E2 | Saddle.toE3 x t ∈ range (D ∘ gc)} ∩ N =
      {x : E2 | Saddle.toE3 x t ∈ (G.trans D) '' sphere (0 : E3) 1} ∩ N at H
    simpa only [hAfiber, hBfiber] using H
  have hmove' (t : Real) (ht : t ∈ Icc (-δ) δ) :
      Psi t '' (d.B c \ C) = d.B (c + t) \ C := by
    have H := hmove t ht
    change Psi t '' ({x : E2 | Saddle.toE3 x 0 ∈ (G.trans D) '' sphere (0 : E3) 1} \ C) =
      {x : E2 | Saddle.toE3 x t ∈ (G.trans D) '' sphere (0 : E3) 1} \ C at H
    simpa only [hBfiber, add_zero] using H
  let Z := d.frame.symm.trans J
  have hZpatch (q : S2) : Z (d.flatten (g q)) = (D ∘ gc) q := by
    change J (d.frame.symm (d.frame (d.D (g q)))) =
      terminalCenteredFlattening d (terminalCenteredFrame d (g q))
    rw [Diffeomorph.symm_apply_apply, terminalCenteredFlattening_apply_frame]
  have hZfiber (x : E2) (t : Real) : Z (Saddle.toE3 x (c + t)) = Saddle.toE3 x t := by
    exact (terminalCenteredFrame_eq_lift_iff d _ x t).mpr
      (d.frame.apply_symm_apply (Saddle.toE3 x (c + t)))
  have hVphysical : (d.flatten ∘ g) '' (e '' closedSquare d.r) ⊆ Z ⁻¹' V := by
    rintro _ ⟨q, hq, rfl⟩
    change Z (d.flatten (g q)) ∈ V
    rw [hZpatch]
    exact hQV ⟨q, hq, rfl⟩
  have hVCphysical (t : Real) (ht : t ∈ Icc (-δ) δ) (x : E2)
      (hx : Saddle.toE3 x (c + t) ∈ Z ⁻¹' V) : x ∈ C := by
    apply hVC t ht x
    change Z (Saddle.toE3 x (c + t)) ∈ V at hx
    rwa [hZfiber] at hx
  exact ⟨δ, C, K, O, N, Z ⁻¹' V, hδ, hδdelta, hC, hCNreg, hK, hO, hCO, hKO,
    hN, hCN, hNNreg, hV.preimage Z.continuous, hVphysical,
    fun t ht x hx => hVCphysical t ht x (hVphysical hx), hVCphysical,
    hsource', hcommonN', Psi, hPsi0, hPsi, hPsiinv, hfix, hfixO, hmove'⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

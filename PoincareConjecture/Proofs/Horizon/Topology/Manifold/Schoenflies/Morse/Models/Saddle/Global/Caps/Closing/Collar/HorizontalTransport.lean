import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.HorizontalProjection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.GraphTransport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Calculus.CompactConjugation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_supported_horizontal_graph_flattening_within
    (D : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞)
    (height : E3 → Real) (baseHeight : E2 → Real)
    (hDh : ∀ z ∈ D.source, height (D z) = baseHeight z.1)
    (a : E2 → Real) {V : Set E2} (hV : IsOpen V) (ha : ContDiffOn Real ∞ a V)
    {K : Set E2} (hK : IsCompact K) (hKV : K ⊆ V)
    {W : Set E3} (hWzero : ∀ z ∈ D.source, D z ∈ W → z.2 = 0)
    (hazero : ∀ y ∈ V, D (y, 0) ∈ W → a y = 0)
    {U : Set E3} (hU : IsOpen U)
    (hsweep : ∀ t ∈ Icc (0 : Real) 1, ∀ y ∈ K,
      (y, (1 - t) * a y) ∈ D.source ∧ D (y, (1 - t) * a y) ∈ U) :
    ∃ S : Set E3, IsCompact S ∧ S ⊆ U ∧ S ⊆ D.target ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧ (∀ z, height (G z) = height z) ∧
        EqOn G id W ∧ ∀ y ∈ K, G (D (y, a y)) = D (y, 0) := by
  let Q := D.source ∩ (V ×ˢ (univ : Set Real))
  have hQ : IsOpen Q := D.open_source.inter (hV.prod isOpen_univ)
  have hopen : IsOpen (Q ∩ D ⁻¹' U) :=
    (D.toOpenPartialHomeomorph.continuousOn.mono inter_subset_left).isOpen_inter_preimage hQ hU
  obtain ⟨S₀, hS₀, hS₀Q, F, hFfix, hFfirst, hFzero, hFmap⟩ :=
    exists_supported_local_graph_flattening_preserving_base a hV ha hK hKV hopen
      (fun t ht y hy => ⟨⟨(hsweep t ht y hy).1, hKV hy, mem_univ _⟩,
        (hsweep t ht y hy).2⟩)
  have hS₀D : S₀ ⊆ D.source := fun z hz => (hS₀Q hz).1.1
  have hFsource : MapsTo F D.source D.source := by
    intro z hz
    by_contra hn
    have hnot : F z ∉ S₀ := fun hh => hn (hS₀D hh)
    have heq : F z = z := F.injective (hFfix (F z) hnot)
    exact hn (heq.symm ▸ hz)
  obtain ⟨G, hGS, hGfix, _, hGcoord, _⟩ :=
    exists_supported_partial_chart_transport D F hS₀ hS₀D hFfix
  refine ⟨D '' S₀, hGS, ?_, ?_, G, hGfix, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact (hS₀Q hz).2
  · rintro _ ⟨z, hz, rfl⟩
    exact D.map_source (hS₀D hz)
  · intro z
    by_cases hz : z ∈ D '' S₀
    · obtain ⟨u, hu, rfl⟩ := hz
      rw [hGcoord u (hS₀D hu), hDh _ (hFsource (hS₀D hu)), hFfirst, hDh _ (hS₀D hu)]
    · rw [hGfix z hz]
  · intro z hzW
    by_cases hz : z ∈ D '' S₀
    · obtain ⟨u, hu, rfl⟩ := hz
      have hu0 := hWzero u (hS₀D hu) hzW
      have heq : u = (u.1, 0) := Prod.ext rfl hu0
      have ha0 : a u.1 = 0 := hazero u.1 (hS₀Q hu).1.2.1 (heq ▸ hzW)
      change G (D u) = D u
      rw [hGcoord u (hS₀D hu)]
      have hf : F u = u := hFzero u.1 u.2 ha0
      rw [hf]
    · exact hGfix z hz
  · intro y hy
    have hsource : (y, a y) ∈ D.source := by
      simpa only [sub_zero, one_mul] using (hsweep 0 (by simp) y hy).1
    rw [hGcoord (y, a y) hsource, hFmap y hy]

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_relative_horizontal_terminal_collar_transport_within
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (i : Fin 3) {N : Set E3} (hN : IsOpen N)
    (hcircleN : (fun y => data.toTerminalSaddleGeometry.filledModel
      (data.modelDisk i y)) '' sphere (0 : E2) 1 ⊆ N) :
    ∃ (c : Real)
      (D : PartialDiffeomorph 𝓘(Real, E2 × Real) (𝓡 3) (E2 × Real) E3 ∞)
      (T : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (O : Set E2) (S : Set E3),
      (c = data.ends.lowerCut ∨ c = data.ends.upperCut) ∧
      sphere (0 : E2) 1 ×ˢ ({0} : Set Real) ⊆ D.source ∧
      (∀ q ∈ sphere (0 : E2) 1,
        D (q, 0) = data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q)) ∧
      (∀ z ∈ D.source, inner Real (M.v : E3) (D z) = c + ‖z.1‖ - 1 ∧
        ‖data.toTerminalSaddleGeometry.filledModel.symm (D z)‖ = 1 + z.2) ∧
      sphere (0 : E2) 1 ⊆ T.source ∧
      T '' sphere (0 : E2) 1 = sphere (0 : E2) 1 ∧
      T.source ⊆ (data.actualDisk i).source ∧
      IsOpen O ∧ sphere (0 : E2) 1 ⊆ O ∧
      IsCompact (closure O) ∧ closure O ⊆ T.target ∧
      (∀ y ∈ closure O, (y, 0) ∈ D.source) ∧
      IsCompact S ∧ S ⊆ N ∧ S ⊆ D.target ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧
        (∀ z, inner Real (M.v : E3) (G z) = inner Real (M.v : E3) z) ∧
        EqOn G id (data.toTerminalSaddleGeometry.flatten ⁻¹'
          data.toTerminalSaddleGeometry.modelBand) ∧
        ∀ y ∈ closure O,
          G (actualCapPhysicalCoordinates data H i (T.symm y)) = D (y, 0) := by
  obtain ⟨c, hc, D, hDs, hDq, hDh, T, a, hTc, hTi, hTs, ha, hac, hgraph, _,
      V, hV, hcV, hVT, hVD, hazero⟩ :=
    exists_actual_terminal_horizontal_graph data hg Φ χ H hH hχ hplanar hlabels i
  let Q := D.source ∩ D ⁻¹' N
  have hQ : IsOpen Q := D.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage
    D.open_source hN
  let q : E2 × Real → E2 × Real := fun z => (z.1, (1 - z.2) * a z.1)
  have hq : ContinuousOn q (V ×ˢ (univ : Set Real)) := continuousOn_fst.prodMk
    ((continuousOn_const.sub continuousOn_snd).mul
      (ha.continuousOn.comp continuousOn_fst (fun z hz => hVT hz.1)))
  have hqopen : IsOpen ((V ×ˢ (univ : Set Real)) ∩ q ⁻¹' Q) :=
    hq.isOpen_inter_preimage (hV.prod isOpen_univ) hQ
  have hqcircle : sphere (0 : E2) 1 ×ˢ Icc (0 : Real) 1 ⊆
      (V ×ˢ (univ : Set Real)) ∩ q ⁻¹' Q := by
    rintro ⟨y, t⟩ ⟨hy, _⟩
    refine ⟨⟨hcV hy, mem_univ _⟩, ?_⟩
    change (y, (1 - t) * a y) ∈ Q
    rw [hac hy, mul_zero]
    refine ⟨hDs ⟨hy, rfl⟩, ?_⟩
    change D (y, 0) ∈ N
    rw [hDq y hy]
    exact hcircleN (mem_image_of_mem _ hy)
  obtain ⟨U, J, hU, _, hcU, hIJ, hUJ⟩ := generalized_tube_lemma
    (isCompact_sphere (0 : E2) 1) isCompact_Icc hqopen hqcircle
  obtain ⟨O, hO, hcO, hOV⟩ := (isCompact_sphere (0 : E2) 1).exists_isOpen_closure_subset
    (((hV.inter hU).inter isOpen_ball).mem_nhdsSet.mpr
      (subset_inter (subset_inter hcV hcU) (sphere_subset_closedBall.trans
        (closedBall_subset_ball (by norm_num : (1 : Real) < 2)))))
  have hOVbase : closure O ⊆ V := fun y hy => (hOV hy).1.1
  have hOc : IsCompact (closure O) := (isCompact_closedBall (0 : E2) 2).of_isClosed_subset
    isClosed_closure (fun x hx => ball_subset_closedBall (hOV hx).2)
  let W := data.toTerminalSaddleGeometry.flatten ⁻¹' data.toTerminalSaddleGeometry.modelBand
  have hWzero (z : E2 × Real) (hz : z ∈ D.source) (hw : D z ∈ W) : z.2 = 0 := by
    have hwhole : data.toTerminalSaddleGeometry.modelBand ⊆
        data.toTerminalSaddleGeometry.flatten ''
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) := by
      rw [data.model_decomposition]
      exact subset_union_left
    obtain ⟨u, ⟨v, hv, rfl⟩, heq⟩ := hwhole hw
    have hphys : data.toTerminalSaddleGeometry.filledModel v = D z :=
      data.toTerminalSaddleGeometry.flatten.injective heq
    have hnorm : ‖data.toTerminalSaddleGeometry.filledModel.symm (D z)‖ = 1 := by
      rw [← hphys, Diffeomorph.symm_apply_apply]
      exact mem_sphere_zero_iff_norm.mp hv
    have hh := (hDh z hz).2
    linarith
  have hsweep : ∀ t ∈ Icc (0 : Real) 1, ∀ y ∈ closure O,
      (y, (1 - t) * a y) ∈ D.source ∧ D (y, (1 - t) * a y) ∈ N := by
    intro t ht y hy
    exact (hUJ (show (y, t) ∈ U ×ˢ J from ⟨(hOV hy).1.2, hIJ ht⟩)).2
  obtain ⟨S, hS, hSN, hSD, G, hGfix, hGheight, hGW, hGmap⟩ :=
    exists_supported_horizontal_graph_flattening_within D
      (inner Real (M.v : E3)) (fun y => c + ‖y‖ - 1)
      (fun z hz => (hDh z hz).1) a hV (ha.mono hVT) hOc hOVbase
      hWzero hazero hN hsweep
  refine ⟨c, D, T, O, S, hc, hDs, hDq, hDh, hTc, hTi, hTs, hO, hcO, hOc,
    hOVbase.trans hVT, fun y hy => hVD y (hOVbase hy), hS, hSN, hSD,
    G, hGfix, hGheight, hGW, ?_⟩
  intro y hy
  rw [(hgraph y (hVT (hOVbase hy))).2]
  exact hGmap y hy

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

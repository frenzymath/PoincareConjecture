import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.FiniteCylindrical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.CoreSeparation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Terminal



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel SphereSurgeryCoreCap Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

private theorem exists_lower_model_terminal_chart
    (data : TerminalSaddleData M P p e) (i : Fin 3)
    (hcut : ∀ x ∈ sphere (0 : E2) 1,
      inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) =
        data.ends.lowerCut) :
    ∃ ε : Real, 0 < ε ∧ ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
      ContMDiffOn IP (𝓡 2) ∞ T T.source ∧
      ContMDiffOn (𝓡 2) IP ∞ T.symm T.target ∧
      univ ×ˢ Icc (data.ends.lowerCut - ε) (data.ends.lowerCut + ε) ⊆ T.source ∧
      (∀ q z, z ∈ Icc (data.ends.lowerCut - ε) (data.ends.lowerCut + ε) →
        inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel (T (q, z))) = z) ∧
      range (fun q : S1 => T (q, data.ends.lowerCut)) = data.modelDisk i '' sphere (0 : E2) 1 ∧
      ∀ q z, z ∈ Ioo (data.ends.lowerCut - ε) data.ends.lowerCut →
        T (q, z) ∈ data.modelDisk i '' ball (0 : E2) 1 := by
  obtain ⟨h, b, q, C, horient, _, _, _, hboundary, _, _, _, _, _, _, _, _,
      ρ, hρ, hρb, _, hfamily⟩ := exists_terminal_model_physical_annulus data i
  have halign : h = (fun q : S2 => inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel q)) ∧ b = data.ends.lowerCut :=
    horient.resolve_right (by
      rintro ⟨hh, hb⟩
      let x : E2 := EuclideanSpace.single 0 1
      have hx : x ∈ sphere (0 : E2) 1 := by simp [x]
      have hu := hboundary x hx
      rw [hh, hb] at hu
      change -inner Real (M.v : E3)
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) = -data.ends.upperCut at hu
      exact data.ends.cuts_lt.ne ((hcut x hx).symm.trans (neg_injective hu)))
  rcases halign with ⟨rfl, rfl⟩
  obtain ⟨δ, hδ, T, hTs, hT, hTi, hTh, _, _, _, hTc, hTneg⟩ := hfamily ρ ⟨hρ, le_rfl⟩
  let c := inner Real (M.v : E3) (data.toTerminalSaddleGeometry.filledModel q) + ρ ^ 2
  let ε := min (δ / 2) ((data.ends.lowerCut - c) / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos (sub_pos.mpr hρb))
  have heδ : ε ≤ δ / 2 := min_le_left _ _
  have hec : ε ≤ (data.ends.lowerCut - c) / 2 := min_le_right _ _
  have hsub : Icc (data.ends.lowerCut - ε) (data.ends.lowerCut + ε) ⊆
      Ioo (c - δ) (data.ends.lowerCut + δ) := by
    intro z hz
    constructor <;> linarith [hz.1, hz.2]
  refine ⟨ε, hε, T, hT, hTi, ?_, fun q z hz => hTh q z (hsub hz), hTc, ?_⟩
  · intro z hz
    rw [hTs]
    exact ⟨hz.1, hsub hz.2⟩
  · intro q z hz
    exact hTneg q z ⟨by linarith [hz.1], hz.2⟩


theorem exists_terminal_lower_family_common_preparation_of_prepared
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (E F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    (hEcore : ∀ D ∈ data.ends.caps, EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q)))
    (hgerms : ∀ i, ∃ U : Set E3, IsOpen U ∧
      (fun x => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) ''
        sphere (0 : E2) 1 ⊆ U ∧
      (E '' range g) ∩ U =
        (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) :
    ∃ r δ : Real, 0 < r ∧ 0 < δ ∧ δ < r ∧
    ∃ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
    ∃ C : data.ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2,
      (∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y) ∧
      (∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, Q y = y) ∧
      EqOn Q id {y | inner Real (M.v : E3) y = data.ends.lowerCut} ∧
      (∀ D ∈ data.ends.caps, EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
      (∀ j, (C j).source = univ ×ˢ Ioo (-r) r) ∧
      (∀ j q z, z ∈ Ioo (-r) r →
        Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
          (data.ends.lowerCut + z) • (M.v : E3) +
            ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
              (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) ∧
      (∀ j, range (fun q : S1 => C j (q, 0)) =
        data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1) ∧
      (∀ j q z, z ∈ Ioo (-r) 0 → C j (q, z) ∈
        data.modelDisk (data.labels.symm (.inl j)) '' ball (0 : E2) 1) ∧
      ∀ j z, z ∈ Icc (data.ends.lowerCut - δ) (data.ends.lowerCut + δ) →
        range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (Q (E (g ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, z)))))) =
        range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
          (E (g (data.ends.lowerCutCircle j q)))) := by
  classical
  let I := data.ends.LowerCutIndex
  let idx : I → Fin 3 := fun j => data.labels.symm (.inl j)
  let m : S2 → E3 := fun q => data.toTerminalSaddleGeometry.filledModel q
  have hlabel (j : I) : data.labels (idx j) = .inl j := data.labels.apply_symm_apply _
  have hidx : Injective idx := data.labels.symm.injective.comp Sum.inl_injective
  have hm : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ m := by
    let D := data.toTerminalSaddleGeometry.filledModel
    have hcoe : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q : S2 => (q : E3)) := contMDiff_coe_sphere
    apply isSmoothEmbedding_of_injective_mfderiv (D.contMDiff.comp hcoe)
      (D.injective.comp Subtype.val_injective)
    intro q
    change Injective (mfderiv (𝓡 2) (𝓡 3) (D ∘ (fun q : S2 => (q : E3))) q)
    rw [mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) _)
      (hcoe.mdifferentiable (by simp) q)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (by convert! injective_mvfderiv_subtypeVal_sphere q)
  have hs : Topology.IsEmbedding (E ∘ g) := E.toHomeomorph.isEmbedding.comp
    (M.tree.embedding_of_mem_leaves hg).isEmbedding
  choose εm hεm T hT hTi hTs hTh hTc hTneg using fun j : I =>
    exists_lower_model_terminal_chart data (idx j)
      (terminal_labeled_model_lower_boundary data Φ χ H hH hχ hplanar hlabels
        (idx j) j (hlabel j)).2
  choose εa hεa hAs hAh using fun j : I =>
    data.ends.exists_lower_terminal_physical_height j.1.1 j.1.2 j.2
  let ε (j : I) := min (εa j) (εm j)
  have hε (j : I) : 0 < ε j := lt_min (hεa j) (hεm j)
  have hεa' (j : I) : ε j ≤ εa j := min_le_left _ _
  have hεm' (j : I) : ε j ≤ εm j := min_le_right _ _
  have hsuba (j : I) : Icc (data.ends.lowerCut - ε j) (data.ends.lowerCut + ε j) ⊆
      Icc (data.ends.lowerCut - εa j) (data.ends.lowerCut + εa j) := by
    intro z hz
    exact ⟨by linarith [hz.1, hεa' j], by linarith [hz.2, hεa' j]⟩
  have hsubm (j : I) : Icc (data.ends.lowerCut - ε j) (data.ends.lowerCut + ε j) ⊆
      Icc (data.ends.lowerCut - εm j) (data.ends.lowerCut + εm j) := by
    intro z hz
    exact ⟨by linarith [hz.1, hεm' j], by linarith [hz.2, hεm' j]⟩
  have hmodelrim (j : I) : range (fun q : S1 => m (T j (q, data.ends.lowerCut))) =
      range (fun q : S1 => m (data.modelDisk (idx j) q)) := by
    change range (m ∘ (fun q : S1 => T j (q, data.ends.lowerCut))) = _
    rw [range_comp, hTc j]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨data.modelDisk (idx j) x, mem_image_of_mem _ x.property, rfl⟩
  have hrim (j : I) : range (fun q : S1 => E (g
      ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, data.ends.lowerCut)))) =
        range (fun q : S1 => m (T j (q, data.ends.lowerCut))) := by
    rw [hmodelrim j]
    simpa only [terminalActualCutCircle, hlabel j, AnnularEndFamily.lowerCutCircle, m] using
      prepared_terminal_labeled_physical_cutCircle_range data Φ χ H hH hχ hplanar hlabels
        E F hFband hFpoint (idx j)
  have hinj : Injective (fun z : I × S1 => T z.1 (z.2, data.ends.lowerCut)) := by
    rintro ⟨i, q⟩ ⟨j, q'⟩ heq
    have hmem (i : I) (q : S1) : data.toTerminalSaddleGeometry.flatten
        (m (T i (q, data.ends.lowerCut))) ∈ data.toTerminalSaddleGeometry.modelCaps (idx i) := by
      have htmem : T i (q, data.ends.lowerCut) ∈ data.modelDisk (idx i) '' sphere (0 : E2) 1 :=
        hTc i ▸ mem_range_self q
      obtain ⟨x, hx, hxeq⟩ := htmem
      rw [← hxeq]
      have hh : data.toTerminalSaddleGeometry.flatten (m (data.modelDisk (idx i) x)) ∈
          data.toTerminalSaddleGeometry.modelCaps (idx i) ∩ data.toTerminalSaddleGeometry.modelBand := by
        rw [data.model_boundary]
        exact mem_image_of_mem _ hx
      exact hh.1
    have hij : i = j := by
      apply hidx
      by_contra hne
      exact disjoint_left.mp (data.model_disjoint hne) (hmem i q)
        (by simpa only [heq] using hmem j q')
    subst j
    have hbase (z : S1) : (z, data.ends.lowerCut) ∈ (T i).source :=
      hTs i ⟨mem_univ _, by linarith [hεm i], by linarith [hεm i]⟩
    exact Prod.ext rfl (congrArg Prod.fst ((T i).injOn (hbase q) (hbase q') heq))
  choose U hU hrimU hsurface using fun j : I => hgerms (idx j)
  have hmrange : range m = data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact mem_image_of_mem _ q.property
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  obtain ⟨R, hR, hRcore⟩ := exists_terminal_core_free_slabs data hg
  obtain ⟨r, δ, hr, _, hδ, hδr, _, Q, C, hQheight,
      ⟨S, hS, hSsupport, hQfix⟩, hcentral, hCs, hC, hcyl, hCrim, hCinside, hconstant⟩ :=
    exists_finite_common_cylindrical_preparation_of_surface_germs
      (norm_eq_of_mem_sphere M.v) hs hm (fun j => data.modelDisk (idx j))
      (fun j : I => (data.ends.lower j.1.1 j.1.2 j.2).chart) T hT hTi
      data.ends.lowerCut ε hε hR
      (fun j z hz => hAs j ⟨hz.1, hsuba j hz.2⟩)
      (fun j z hz => hTs j ⟨hz.1, hsubm j hz.2⟩)
      (fun j q z hz => (hEheight _).trans (hAh j q z (hsuba j hz)))
      (fun j q z hz => hTh j q z (hsubm j hz)) hTc
      (fun j q z hz => hTneg j q z ⟨by linarith [hz.1, hεm' j], hz.2⟩)
      hinj hrim U hU
      (by
        intro j
        simp only [Function.comp_apply]
        rw [hrim j, hmodelrim j]
        rintro y ⟨q, rfl⟩
        exact hrimU j (mem_image_of_mem _ q.property))
      (by intro j; rw [range_comp, hmrange]; exact hsurface j)
  refine ⟨r, δ, hr, hδ, hδr, Q, C, hQheight, ⟨S, hS, hQfix⟩, hcentral, ?_, hCs, ?_, hCrim,
    hCinside, ?_⟩
  · intro D hD q hq
    change Q (E (g q)) = g q
    rw [show E (g q) = g q from hEcore D hD hq]
    apply hQfix
    intro hmem
    exact (not_le_of_gt (hRcore data.ends.lowerCut (Or.inl rfl) D hD q hq)) (hSsupport hmem)
  · intro j q z hz
    have hh := hcyl j q z hz
    simpa only [hC, add_zero, m] using hh
  · intro j z hz
    exact hconstant j z hz





theorem exists_terminal_lower_family_common_preparation
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχsmooth : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∃ E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y) ∧
      (∀ D ∈ data.ends.caps, EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
      ∃ K : Set E3, IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧ EqOn F id data.toTerminalSaddleGeometry.modelBand ∧
        (∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
          data.toTerminalSaddleGeometry.flatten (E (g q))) ∧
        (∀ i, F '' (H '' data.toTerminalSaddleGeometry.C i) =
          (data.toTerminalSaddleGeometry.flatten ∘ E ∘ g) ''
            terminalEndCap data.ends (data.labels i)) ∧
        ∃ r δ : Real, 0 < r ∧ 0 < δ ∧ δ < r ∧
        ∃ Q : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        ∃ C : data.ends.LowerCutIndex → OpenPartialHomeomorph (S1 × Real) S2,
          (∀ y, inner Real (M.v : E3) (Q y) = inner Real (M.v : E3) y) ∧
          (∃ S : Set E3, IsCompact S ∧ ∀ y ∉ S, Q y = y) ∧
          EqOn Q id {y | inner Real (M.v : E3) y = data.ends.lowerCut} ∧
          (∀ D ∈ data.ends.caps, EqOn (Q ∘ E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
          (∀ j, (C j).source = univ ×ˢ Ioo (-r) r) ∧
          (∀ j q z, z ∈ Ioo (-r) r →
            Q (data.toTerminalSaddleGeometry.filledModel (C j (q, z))) =
              (data.ends.lowerCut + z) • (M.v : E3) +
                ((Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
                  (data.toTerminalSaddleGeometry.filledModel (C j (q, 0))) : E3)) ∧
          (∀ j, range (fun q : S1 => C j (q, 0)) =
            data.modelDisk (data.labels.symm (.inl j)) '' sphere (0 : E2) 1) ∧
          (∀ j q z, z ∈ Ioo (-r) 0 → C j (q, z) ∈
            data.modelDisk (data.labels.symm (.inl j)) '' ball (0 : E2) 1) ∧
          ∀ j z, z ∈ Icc (data.ends.lowerCut - δ) (data.ends.lowerCut + δ) →
            range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
              (Q (E (g ((data.ends.lower j.1.1 j.1.2 j.2).chart (q, z)))))) =
            range (fun q : S1 => (Hemisphere.Plane (M.v : E3)).orthogonalProjectionOnto
              (E (g (data.ends.lowerCutCircle j q)))) := by
  obtain ⟨E, hEheight, hEcore, hgerms, K, hK, F, hFfix, hFband, hFpoint, hFcap, _⟩ :=
    exists_prepared_terminal_cap_replacements data hg Φ hzero hΦ hΦinv χ hχsmooth H
      hH hχ hplanar hlabels
  refine ⟨E, hEheight, hEcore, K, hK, F, hFfix, hFband, hFpoint, hFcap, ?_⟩
  apply exists_terminal_lower_family_common_preparation_of_prepared data hg Φ χ H
    hH hχ hplanar hlabels E F hEheight hEcore hFband hFpoint
  intro i
  obtain ⟨U, hU, hrim, _, hsurface⟩ := hgerms i
  exact ⟨U, hU, hrim, hsurface⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

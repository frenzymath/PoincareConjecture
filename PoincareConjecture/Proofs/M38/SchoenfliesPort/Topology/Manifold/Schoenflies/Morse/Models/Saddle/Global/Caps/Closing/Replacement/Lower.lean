import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.LowerReplacement
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.Model.TerminalAnnulus
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.LabelAlignment







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Saddle
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps
open _root_.Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SaddleLevel SphereSurgeryCoreCap _root_.Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}



theorem prepared_terminal_labeled_physical_cutCircle_range
    (data : TerminalSaddleData M P p e)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand)
    (E F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q))) (i : Fin 3) :
    range (fun q : S1 => E (g (terminalActualCutCircle data i q))) =
      range (fun q : S1 => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q)) := by
  have hrange := terminal_labeled_cutCircle_range data Φ χ H hH hχ hplanar hlabels i
  have hfix (q : S1) : F (H (data.toTerminalSaddleGeometry.flatten
      (g (terminalActualCutCircle data i q)))) =
      H (data.toTerminalSaddleGeometry.flatten (g (terminalActualCutCircle data i q))) := by
    apply hFband
    have hh : H (data.toTerminalSaddleGeometry.flatten (g (terminalActualCutCircle data i q))) ∈
        range (fun q : S1 => data.toTerminalSaddleGeometry.flatten
          (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i q))) :=
      hrange ▸ mem_range_self q
    obtain ⟨r, hr⟩ := hh
    rw [← hr]
    have hb : data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i r)) ∈
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand := by
      rw [data.model_boundary i]
      exact mem_image_of_mem _ r.property
    exact hb.2
  have hpoint (q : S1) : E (g (terminalActualCutCircle data i q)) =
      data.toTerminalSaddleGeometry.flatten.symm
        (H (data.toTerminalSaddleGeometry.flatten (g (terminalActualCutCircle data i q)))) := by
    have hh := hFpoint (terminalActualCutCircle data i q)
    rw [hfix q] at hh
    simpa only [Diffeomorph.symm_apply_apply] using
      (congrArg data.toTerminalSaddleGeometry.flatten.symm hh).symm
  rw [show (fun q : S1 => E (g (terminalActualCutCircle data i q))) =
      (fun q : S1 => data.toTerminalSaddleGeometry.flatten.symm
        (H (data.toTerminalSaddleGeometry.flatten (g (terminalActualCutCircle data i q))))) from
          funext hpoint]
  exact terminal_labeled_physical_cutCircle_range data Φ χ H hH hχ hplanar hlabels i





theorem exists_buffered_prepared_terminal_lower_cap_replacement
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
    (E F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    (hEcore : ∀ D ∈ data.ends.caps,
      EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q)))
    (i : Fin 3) (j : data.ends.LowerCutIndex) (hlabel : data.labels i = Sum.inl j)
    {U : Set E3} (hU : IsOpen U)
    (hrimU : (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
      sphere (0 : E2) 1 ⊆ U)
    (hsurface : (E '' range g) ∩ U =
      (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, R y = y) ∧
        (∃ η : Real, 0 < η ∧
          EqOn R id {y | data.ends.lowerCut - η ≤ inner Real (M.v : E3) y}) ∧
        R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps i := by
  let m : S2 → E3 := fun q => data.toTerminalSaddleGeometry.filledModel q
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
  have hg₀ := M.tree.embedding_of_mem_leaves hg
  have hge : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (E ∘ g) := by
    apply isSmoothEmbedding_of_injective_mfderiv (E.contMDiff.comp hg₀.contMDiff)
      (E.injective.comp hg₀.isEmbedding.injective)
    intro q
    rw [mfderiv_comp q (E.contMDiff.mdifferentiable (by simp) _)
      (hg₀.contMDiff.mdifferentiable (by simp) _)]
    exact (E.mfderivToContinuousLinearEquiv (by simp) _).injective.comp
      (injective_mfderiv_sphere_embedding hg₀ q)
  have hheight (q : S2) : inner Real (M.v : E3) ((E ∘ g) q) =
      inner Real (M.v : E3) (g q) := hEheight (g q)
  let A := (data.ends.lower j.1.1 j.1.2 j.2).congrEmbedding
    (hEcore j.1.1 j.1.2) hheight
  have hgerm : ∀ q ∈ P.core, data.ends.height =ᶠ[𝓝 q]
      (fun x => inner Real (M.v : E3) ((E ∘ g) x)) := by
    simpa only [hheight] using data.ends.height_germ
  obtain ⟨h, b, q, C, horient, _, hq, hqb, hboundary, hunique, hcomponent,
      hregular, hC0, hCq, hC, hCi, hform, ρ, hρ, hρb, _, hfamily⟩ :=
    exists_terminal_model_physical_annulus data i
  have hlower := terminal_labeled_model_lower_boundary
    data Φ χ H hH hχ hplanar hlabels i j hlabel
  have horientLower : h = (fun q : S2 => inner Real (M.v : E3) (m q)) ∧
      b = data.ends.lowerCut := horient.resolve_right (by
    rintro ⟨hh, hb⟩
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2) (x := 0)).mpr
      (show (0 : Real) ≤ 1 by norm_num)
    have hupper := hboundary x hx
    rw [hh, hb] at hupper
    have hlo := hlower.2 x hx
    change -inner Real (M.v : E3)
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i x)) =
        -data.ends.upperCut at hupper
    exact data.ends.cuts_lt.ne (hlo.symm.trans (neg_injective hupper)))
  rcases horientLower with ⟨rfl, rfl⟩
  obtain ⟨δ, hδ, T, hTs, hT, hTi, hTh, _, _, _, hTc, hTneg⟩ := hfamily ρ ⟨hρ, le_rfl⟩
  let ε := min (δ / 2) ((data.ends.lowerCut - (inner Real (M.v : E3) (m q) + ρ^2)) / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos (sub_pos.mpr hρb))
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεgap : ε ≤ (data.ends.lowerCut - (inner Real (M.v : E3) (m q) + ρ^2)) / 2 :=
    min_le_right _ _
  have hsub : Icc (data.ends.lowerCut - ε) (data.ends.lowerCut + ε) ⊆
      Ioo (inner Real (M.v : E3) (m q) + ρ^2 - δ) (data.ends.lowerCut + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hArim (z : S1) : terminalActualCutCircle data i z = A.chart (z, data.ends.lowerCut) := by
    simp only [terminalActualCutCircle, hlabel]
    rfl
  have hrimPrepared : range (fun z : S1 => (E ∘ g) (A.chart (z, data.ends.lowerCut))) =
      range (fun z : S1 => m (data.modelDisk i z)) := by
    simpa only [hArim, Function.comp_apply] using
      prepared_terminal_labeled_physical_cutCircle_range data Φ χ H hH hχ hplanar hlabels
        E F hFband hFpoint i
  have hmodelrim : range (fun z : S1 => m (T (z, data.ends.lowerCut))) =
      range (fun z : S1 => m (data.modelDisk i z)) := by
    change range (m ∘ (fun z : S1 => T (z, data.ends.lowerCut))) = _
    rw [range_comp, hTc]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨data.modelDisk i x, mem_image_of_mem _ x.property, rfl⟩
  have hmodelRange : range m = data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1 := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact mem_image_of_mem _ q.property
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
  obtain ⟨K, hK, R, hRfix, hRhalf, hRimage⟩ :=
    exists_buffered_relative_lower_end_replacement_of_surface_germ A hge
      (data.ends.cap_center_bounds j.1.1 j.1.2).1.le j.2 hgerm hm
      (data.modelDisk i) (data.modelDisk_source i) hq hqb hboundary hunique
      (data.modelSeed i) hcomponent hregular C hC0 hCq hC hCi hform T hT hTi hε
      (fun z hz => by rw [hTs]; exact ⟨hz.1, hsub hz.2⟩)
      (fun z t ht => hTh z t (hsub ht)) hTc
      (fun z t ht => hTneg z t ⟨by linarith [ht.1], ht.2⟩)
      (hrimPrepared.trans hmodelrim.symm) hU
      (by rw [hrimPrepared]; rintro y ⟨z, rfl⟩; exact hrimU (mem_image_of_mem _ z.property))
      (by rw [range_comp, hmodelRange]; exact hsurface)
  have hcap : terminalEndCap data.ends (data.labels i) = A.cappedRegion data.ends.lowerCut := by
    rw [hlabel]
    change A.region ∪ _ = _
    exact union_comm _ _
  have hmodel : m '' (data.modelDisk i '' closedBall (0 : E2) 1) =
      data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelCaps i := by
    rw [data.modelDisk_image]
    change m '' data.toTerminalSaddleGeometry.modelDomain i =
      data.toTerminalSaddleGeometry.flatten.symm ''
        ((data.toTerminalSaddleGeometry.flatten ∘ m) '' data.toTerminalSaddleGeometry.modelDomain i)
    rw [image_image]
    exact image_congr (fun q _ =>
      (data.toTerminalSaddleGeometry.flatten.symm_apply_apply (m q)).symm)
  exact ⟨K, hK, R, hRfix, hRhalf, by rwa [hcap, ← hmodel]⟩


theorem exists_prepared_terminal_lower_cap_replacement
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
    (E F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hEheight : ∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y)
    (hEcore : ∀ D ∈ data.ends.caps,
      EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1))
    (hFband : EqOn F id data.toTerminalSaddleGeometry.modelBand)
    (hFpoint : ∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
      data.toTerminalSaddleGeometry.flatten (E (g q)))
    (i : Fin 3) (j : data.ends.LowerCutIndex) (hlabel : data.labels i = Sum.inl j)
    {U : Set E3} (hU : IsOpen U)
    (hrimU : (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
      sphere (0 : E2) 1 ⊆ U)
    (hsurface : (E '' range g) ∩ U =
      (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, R y = y) ∧
        EqOn R id {y | data.ends.lowerCut ≤ inner Real (M.v : E3) y} ∧
        R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps i := by
  obtain ⟨K, hK, R, hR, ⟨η, hη, hu⟩, hi⟩ :=
    exists_buffered_prepared_terminal_lower_cap_replacement data hg Φ χ H hH hχ hplanar
      hlabels E F hEheight hEcore hFband hFpoint i j hlabel hU hrimU hsurface
  refine ⟨K, hK, R, hR, ?_, hi⟩
  intro y hy
  apply hu
  change data.ends.lowerCut - η ≤ inner Real (M.v : E3) y
  change data.ends.lowerCut ≤ inner Real (M.v : E3) y at hy
  linarith

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies

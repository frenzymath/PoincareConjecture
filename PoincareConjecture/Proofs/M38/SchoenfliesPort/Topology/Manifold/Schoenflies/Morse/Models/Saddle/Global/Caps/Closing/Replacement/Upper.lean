import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Replacement.Lower
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.BufferedUpperReplacement







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

private def reverseUpperTime : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞ where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  contMDiff_toFun := contMDiff_id.neg
  contMDiff_invFun := contMDiff_id.neg

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

set_option maxHeartbeats 2000000 in



theorem exists_buffered_prepared_terminal_upper_cap_replacement
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
    (i : Fin 3) (j : data.ends.UpperCutIndex) (hlabel : data.labels i = Sum.inr j)
    {U : Set E3} (hU : IsOpen U)
    (hrimU : (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
      sphere (0 : E2) 1 ⊆ U)
    (hsurface : (E '' range g) ∩ U =
      (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, R y = y) ∧
        (∃ η : Real, 0 < η ∧
          EqOn R id {y | inner Real (M.v : E3) y ≤ data.ends.upperCut + η}) ∧
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
  let A := (data.ends.upper j.1.1 j.1.2 j.2).congrEmbedding
    (hEcore j.1.1 j.1.2) hheight
  have hgerm : ∀ q ∈ P.core, data.ends.height =ᶠ[𝓝 q]
      (fun x => inner Real (M.v : E3) ((E ∘ g) x)) := by
    simpa only [hheight] using data.ends.height_germ
  obtain ⟨h, b, q, C, horient, _, hq, hqb, hboundary, hunique, hcomponent,
      hregular, hC0, hCq, hC, hCi, hform, ρ, hρ, hρb, _, hfamily⟩ :=
    exists_terminal_model_physical_annulus data i
  have hupper := terminal_labeled_model_upper_boundary
    data Φ χ H hH hχ hplanar hlabels i j hlabel
  have horientUpper : h = -(fun q : S2 => inner Real (M.v : E3) (m q)) ∧
      b = -data.ends.upperCut := horient.resolve_left (by
    rintro ⟨hh, hb⟩
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (E := E2) (x := 0)).mpr
      (show (0 : Real) ≤ 1 by norm_num)
    have hlo := hboundary x hx
    rw [hh, hb] at hlo
    exact data.ends.cuts_lt.ne (hlo.symm.trans (hupper.2 x hx)))
  rcases horientUpper with ⟨rfl, rfl⟩
  obtain ⟨δ, hδ, T₀, hT₀s, hT₀, hT₀i, hT₀h, _, _, _, hT₀c, hT₀neg⟩ :=
    hfamily ρ ⟨hρ, le_rfl⟩
  let ε := min (δ / 2)
    ((-data.ends.upperCut - (-inner Real (M.v : E3) (m q) + ρ^2)) / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos (sub_pos.mpr hρb))
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεgap : ε ≤ (-data.ends.upperCut - (-inner Real (M.v : E3) (m q) + ρ^2)) / 2 :=
    min_le_right _ _
  have hsub {z : Real} (hz : z ∈ Icc (data.ends.upperCut - ε) (data.ends.upperCut + ε)) :
      -z ∈ Ioo (-inner Real (M.v : E3) (m q) + ρ^2 - δ) (-data.ends.upperCut + δ) := by
    constructor <;> linarith [hz.1, hz.2]
  let Q := (Diffeomorph.refl (𝓡 1) S1 (n := ∞)).prodCongr reverseUpperTime
  let P₀ : PartialDiffeomorph IP (𝓡 2) (S1 × Real) S2 ∞ :=
    { T₀ with contMDiffOn_toFun := hT₀, contMDiffOn_invFun := hT₀i }
  let P₁ := Q.toPartialDiffeomorph.trans P₀
  let T := P₁.toOpenPartialHomeomorph
  have hTchart (z : S1) (t : Real) : T (z, t) = T₀ (z, -t) := rfl
  have hTs : univ ×ˢ Icc (data.ends.upperCut - ε) (data.ends.upperCut + ε) ⊆ T.source := by
    rintro ⟨z, t⟩ ⟨_, ht⟩
    change (z, t) ∈ univ ∧ (z, -t) ∈ T₀.source
    rw [hT₀s]
    exact ⟨mem_univ _, mem_univ _, hsub ht⟩
  have hTh (z : S1) (t : Real) (ht : t ∈ Icc (data.ends.upperCut - ε) (data.ends.upperCut + ε)) :
      inner Real (M.v : E3) (m (T (z, t))) = t := by
    have hh := hT₀h z (-t) (hsub ht)
    change -inner Real (M.v : E3) (m (T₀ (z, -t))) = -t at hh
    exact neg_injective hh
  have hTc : range (fun z : S1 => T (z, data.ends.upperCut)) =
      data.modelDisk i '' sphere (0 : E2) 1 := hT₀c
  have hTpos (z : S1) (t : Real) (ht : t ∈ Ioo data.ends.upperCut (data.ends.upperCut + ε)) :
      T (z, t) ∈ data.modelDisk i '' ball (0 : E2) 1 :=
    hT₀neg z (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hArim (z : S1) : terminalActualCutCircle data i z = A.chart (z, data.ends.upperCut) := by
    simp only [terminalActualCutCircle, hlabel]
    rfl
  have hrimPrepared : range (fun z : S1 => (E ∘ g) (A.chart (z, data.ends.upperCut))) =
      range (fun z : S1 => m (data.modelDisk i z)) := by
    simpa only [hArim, Function.comp_apply] using
      prepared_terminal_labeled_physical_cutCircle_range data Φ χ H hH hχ hplanar hlabels
        E F hFband hFpoint i
  have hmodelrim : range (fun z : S1 => m (T (z, data.ends.upperCut))) =
      range (fun z : S1 => m (data.modelDisk i z)) := by
    change range (m ∘ (fun z : S1 => T (z, data.ends.upperCut))) = _
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
  have hunique' : ∀ x ∈ data.modelDisk i '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (m q)) x = 0 → x = q := by
    intro x hx hc
    exact hunique x hx (by simpa only [mfderiv_neg, neg_eq_zero] using hc)
  have hcomponent' : data.modelDisk i '' closedBall 0 1 =
      closure (connectedComponentIn ((fun q => inner Real (M.v : E3) (m q)) ⁻¹'
        Ioi data.ends.upperCut) (data.modelSeed i)) := by
    convert hcomponent using 2
    congr 1
    ext x
    simp only [mem_preimage, mem_Iio, mem_Ioi, Pi.neg_apply, neg_lt_neg_iff]
  have hregular' : ∀ x, inner Real (M.v : E3) (m x) = data.ends.upperCut →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real (M.v : E3) (m q)) x ≠ 0 := by
    intro x hx
    have hh := hregular x (congrArg Neg.neg hx)
    simpa only [mfderiv_neg, neg_ne_zero] using hh
  obtain ⟨K, hK, R, hRfix, hRhalf, hRimage⟩ :=
    exists_buffered_relative_upper_end_replacement_of_surface_germ A hge
      (data.ends.cap_center_bounds j.1.1 j.1.2).2.le j.2 hgerm hm
      (data.modelDisk i) (data.modelDisk_source i) hq
      (by simpa only [Pi.neg_apply, neg_lt_neg_iff] using hqb)
      (fun x hx => neg_injective (hboundary x hx)) hunique'
      (data.modelSeed i) hcomponent' hregular' C hC0 hCq hC hCi
      (fun x hx => by have hh := hform x hx; dsimp only [Pi.neg_apply] at hh; linarith)
      T P₁.contMDiffOn P₁.symm.contMDiffOn hε hTs hTh hTc hTpos
      (hrimPrepared.trans hmodelrim.symm) hU
      (by rw [hrimPrepared]; rintro y ⟨z, rfl⟩; exact hrimU (mem_image_of_mem _ z.property))
      (by rw [range_comp, hmodelRange]; exact hsurface)
  have hcap : terminalEndCap data.ends (data.labels i) = A.cappedRegion data.ends.upperCut := by
    rw [hlabel]
    change A.region ∪ _ = _
    rw [A.region_eq_image, UpperAnnularEnd.cappedRegion, union_comm]
    rfl
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

set_option maxHeartbeats 2000000 in


theorem exists_prepared_terminal_upper_cap_replacement
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
    (i : Fin 3) (j : data.ends.UpperCutIndex) (hlabel : data.labels i = Sum.inr j)
    {U : Set E3} (hU : IsOpen U)
    (hrimU : (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
      sphere (0 : E2) 1 ⊆ U)
    (hsurface : (E '' range g) ∩ U =
      (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ R : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, R y = y) ∧
        EqOn R id {y | inner Real (M.v : E3) y ≤ data.ends.upperCut} ∧
        R '' ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) =
          data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps i := by
  obtain ⟨K, hK, R, hR, ⟨η, hη, hu⟩, hi⟩ :=
    exists_buffered_prepared_terminal_upper_cap_replacement data hg Φ χ H hH hχ hplanar
      hlabels E F hEheight hEcore hFband hFpoint i j hlabel hU hrimU hsurface
  refine ⟨K, hK, R, hR, ?_, hi⟩
  intro y hy
  apply hu
  change inner Real (M.v : E3) y ≤ data.ends.upperCut + η
  change inner Real (M.v : E3) y ≤ data.ends.upperCut at hy
  linarith

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies

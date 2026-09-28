import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.EndBall.TerminalHeight
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.LowerNormalization
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function TopologicalSpace
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SphereSurgeryCoreCap Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private theorem chart_of_local_diffeomorph_on_open
    (f : S1 × Real → S2) {W : Set (S1 × Real)} (hW : IsOpen W)
    (hi : InjOn f W) (hl : ∀ x ∈ W, IsLocalDiffeomorphAt IP (𝓡 2) ∞ f x) :
    ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
      T.source = W ∧ ContMDiffOn IP (𝓡 2) ∞ T T.source ∧
      ContMDiffOn (𝓡 2) IP ∞ T.symm T.target ∧ ∀ x, T x = f x := by
  let U : Opens (S1 × Real) := ⟨W, hW⟩
  have hf : IsLocalDiffeomorph IP (𝓡 2) ∞ (fun x : U => f x) := fun x =>
    (Poincare.isLocalDiffeomorph_opensSubtypeVal IP U x).comp (𝓡 2) S2
      (hl x x.property)
  let T : OpenPartialHomeomorph (S1 × Real) S2 :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv f W)
      (fun x hx => (hl x hx).contMDiffAt.continuousAt.continuousWithinAt)
      hf.isOpenMap hW
  refine ⟨T, rfl, fun x hx => (hl x hx).contMDiffAt.contMDiffWithinAt, ?_, fun _ => rfl⟩
  intro y hy
  let x := T.symm y
  have hx : x ∈ W := T.map_target hy
  have hlocal := hl x hx
  have hxy : f x = y := T.right_inv hy
  have heq : T.symm =ᶠ[𝓝 y] hlocal.localInverse := by
    have hc := T.continuousAt_symm hy
    filter_upwards [T.open_target.mem_nhds hy,
      hc.preimage_mem_nhds (hlocal.localInverse.open_target.mem_nhds
        hlocal.localInverse_mem_target)] with z hz hzin
    exact (hlocal.localInverse_left_inv hzin).symm.trans
      (congrArg hlocal.localInverse (T.right_inv hz))
  have hs : ContMDiffAt (𝓡 2) IP ∞ hlocal.localInverse y := by
    rw [← hxy]
    exact hlocal.localInverse_contMDiffAt
  exact (hs.congr_of_eventuallyEq heq).contMDiffWithinAt

theorem exists_lower_terminal_end_normalization
    {v : E3} {g : S2 → E3} {B : Set Real}
    {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}
    (A : LowerAnnularEnd D C h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (haD : a ≤ D.center) (hDb : D.center < b)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q))) :
    ∃ d δ : Real, d < D.center ∧ 0 < δ ∧
      ∃ T : OpenPartialHomeomorph (S1 × Real) S2,
      ∃ L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        T.source = univ ×ˢ Ioo (d - δ) (b + δ) ∧
        ContMDiffOn IP (𝓡 2) ∞ T T.source ∧
        ContMDiffOn (𝓡 2) IP ∞ T.symm T.target ∧
        (∀ x, T x = A.chart x) ∧
        (∀ q t, t ∈ Ioo (d - δ) (b + δ) → inner Real v (g (T (q, t))) = t) ∧
        (∀ t ∈ Icc d D.center,
          range (fun q : S1 => (Hemisphere.Plane v).orthogonalProjectionOnto (g (T (q, t)))) =
            D.planeMap '' sphere (0 : Hemisphere.Plane v) 1) ∧
        (∀ y, d ≤ inner Real v y → L y = y) ∧
        (∀ y, (Hemisphere.Plane v).orthogonalProjectionOnto (L y) =
          (Hemisphere.Plane v).orthogonalProjectionOnto y) ∧
        L '' (g '' A.cappedRegion b) =
          (liftPlaneDiffeomorph D.unit_v d D.scale D.scale_ne_zero D.planeMap ''
            boundedCylinderNorthernCap v) ∪
          g '' (T '' (univ ×ˢ Icc d b)) := by
  let c := (D.center + b) / 2
  have hDc : D.center < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hcapgerm : ∀ p ∈ D.chart '' sphere (0 : E2) 1,
      h =ᶠ[𝓝 p] (fun q => inner Real v (g q)) := by
    intro p hp
    obtain ⟨q, rfl⟩ := A.boundary.symm ▸ hp
    exact hgerm _ (A.retained (mem_image_of_mem A.chart ⟨mem_univ _, le_rfl, hDb.le⟩))
  obtain ⟨δ₀, η, hδ₀, hη, hη1, T₀, hT₀s, hT₀, hT₀i, hT₀A, hheight₀,
    hcut, hcircles, L, _, hLlocal, hLproj, hLend, _⟩ :=
    Saddle.Wall.Smoothing.Exterior.Caps.exists_lower_end_relative_normalization
      A hg haD hDc hcb hcapgerm
  let d := D.center + D.scale * η
  have hdD : d < D.center := by dsimp [d]; nlinarith [A.scale_neg]
  have hdl : D.center - δ₀ < d := hcut.1
  have hLfix (y : E3) (hy : d ≤ inner Real v y) : L y = y :=
    (hLlocal y hy).eq_of_nhds
  obtain ⟨ε, hε, _, hterminal⟩ :=
    A.exists_physical_height_at_terminal (haD.trans hDb.le) hDb.le hgerm
  let δ := min ((d - (D.center - δ₀)) / 2) (min (ε / 2) (A.delta / 2))
  have hδ : 0 < δ := lt_min (half_pos (sub_pos.mpr hdl))
    (lt_min (half_pos hε) (half_pos A.delta_pos))
  have hδold : δ < d - (D.center - δ₀) :=
    (min_le_left _ _).trans_lt (by linarith)
  have hδε : δ < ε := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hδA : δ < A.delta :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith [A.delta_pos])
  let W : Set (S1 × Real) := univ ×ˢ Ioo (d - δ) (b + δ)
  have hsource₀ (q : S1) (t : Real) (ht : t ∈ Ioo (d - δ) (b + δ))
      (htD : t < D.center) : (q, t) ∈ T₀.source := by
    rw [hT₀s]
    exact ⟨mem_univ _, by linarith [ht.1], by linarith⟩
  have hsourceA (q : S1) (t : Real) (ht : t ∈ Ioo (d - δ) (b + δ))
      (hDt : D.center ≤ t) : (q, t) ∈ A.chart.source := by
    rw [A.source]
    exact ⟨mem_univ _, by linarith [A.delta_pos], by linarith [ht.2]⟩
  have hphysical (q : S1) (t : Real) (ht : t ∈ Ioo (d - δ) (b + δ)) :
      inner Real v (g (A.chart (q, t))) = t := by
    by_cases htD : t < D.center
    · rw [← hT₀A]
      exact hheight₀ q t ((hT₀s ▸ hsource₀ q t ht htD).2)
    by_cases htb : t ≤ b
    · exact A.actual_height q t ⟨le_of_not_gt htD, htb⟩
    exact hterminal q t ⟨by linarith [le_of_not_ge htb], by linarith [ht.2]⟩
  let P₀ : PartialDiffeomorph IP (𝓡 2) (S1 × Real) S2 ∞ :=
    { T₀ with contMDiffOn_toFun := hT₀, contMDiffOn_invFun := hT₀i }
  let PA : PartialDiffeomorph IP (𝓡 2) (S1 × Real) S2 ∞ :=
    { A.chart with contMDiffOn_toFun := A.smooth, contMDiffOn_invFun := A.symm_smooth }
  have hlocal (z : S1 × Real) (hz : z ∈ W) :
      IsLocalDiffeomorphAt IP (𝓡 2) ∞ A.chart z := by
    by_cases htD : z.2 < D.center
    · have hf : (T₀ : S1 × Real → S2) = A.chart := funext hT₀A
      rw [← hf]
      exact P₀.isLocalDiffeomorphAt IP (𝓡 2) ∞ (hsource₀ z.1 z.2 hz.2 htD)
    exact PA.isLocalDiffeomorphAt IP (𝓡 2) ∞
      (hsourceA z.1 z.2 hz.2 (le_of_not_gt htD))
  have hinj : InjOn A.chart W := by
    rintro ⟨q, t⟩ hqt ⟨r, u⟩ hru heq
    have htu : t = u := (hphysical q t hqt.2).symm.trans
      ((congrArg (fun p => inner Real v (g p)) heq).trans (hphysical r u hru.2))
    subst u
    by_cases htD : t < D.center
    · exact T₀.injOn (hsource₀ q t hqt.2 htD) (hsource₀ r t hru.2 htD)
        (by simpa only [hT₀A] using heq)
    exact A.chart.injOn (hsourceA q t hqt.2 (le_of_not_gt htD))
      (hsourceA r t hru.2 (le_of_not_gt htD)) heq
  obtain ⟨T, hTs, hT, hTi, hTA⟩ := chart_of_local_diffeomorph_on_open A.chart
    (isOpen_univ.prod isOpen_Ioo) hinj hlocal
  have hsplit : A.cappedRegion b = A.cappedRegion c ∪ A.chart '' (univ ×ˢ Icc c b) := by
    unfold LowerAnnularEnd.cappedRegion
    rw [union_assoc, ← image_union, ← prod_union, Icc_union_Icc_eq_Icc hDc.le hcb.le]
  have htailfix : EqOn L id (g '' (A.chart '' (univ ×ˢ Icc c b))) := by
    rintro _ ⟨_, ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩, rfl⟩
    apply hLfix
    rw [A.actual_height q t ⟨hDc.le.trans ht.1, ht.2⟩]
    exact hdD.le.trans (hDc.le.trans ht.1)
  refine ⟨d, δ, hdD, hδ, T, L, hTs, hT, hTi, hTA,
    (by intro q t ht; rw [hTA]; exact hphysical q t ht), ?_, hLfix, hLproj, ?_⟩
  · intro t ht
    let θ := (t - D.center) / D.scale
    have hθ : θ ∈ Icc (0 : Real) η := by
      refine ⟨div_nonneg_of_nonpos (by linarith [ht.2]) A.scale_neg.le,
        (div_le_iff_of_neg A.scale_neg).mpr ?_⟩
      have hdt : D.center + D.scale * η ≤ t := ht.1
      linarith
    have heq : D.center + D.scale * θ = t := by
      dsimp [θ]
      field_simp [D.scale_ne_zero]
      ring
    simpa only [hTA, hT₀A, heq] using hcircles θ hθ
  · rw [hsplit, image_union, image_union, image_congr htailfix, image_id]
    have hfun₀ : (T₀ : S1 × Real → S2) = A.chart := funext hT₀A
    have hfun : (T : S1 × Real → S2) = A.chart := funext hTA
    rw [hLend, hfun₀, hfun, union_assoc, ← image_union, ← image_union,
      ← prod_union, Icc_union_Icc_eq_Icc (hdD.le.trans hDc.le) hcb.le]

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies

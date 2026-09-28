import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.SelectedData
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.TerminalInputs
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.EndOrientation
import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.EndCount

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar
open PlaneArcs.Terminal PlaneArcs.Terminal.Reflection
open SphereSurgeryCoreCap Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def FullPlanarFamily {f : S2 → E3} {p : S2} (s : TerminalInputData f p) : Prop :=
  ∃ data : TerminalSaddleData s.reduction s.path p s.chart,
    let d := data.toTerminalSaddleGeometry
    ∃ (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
      (K : Set E2) (χ : Real → Real),
      (∀ z x, Φ 0 z x = x) ∧
      ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2) ∧
      ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2) ∧
      IsCompact K ∧ (∀ u z x, x ∉ K → Φ u z x = x) ∧
      ContDiff Real ∞ χ ∧ (∀ z ∈ d.I, χ z = 1) ∧
      (∀ z ∈ d.I, Φ 1 z '' d.A z = d.B z) ∧
      (∀ i, planarHeightMap Φ 1 '' (d.C i ∩ d.actualBand) =
        d.modelCaps i ∩ d.modelBand) ∧
      ∃ ρ > 0, ∃ U : Set E3, IsOpen U ∧ closedSquare ρ ⊆ s.chart.source ∧
        (∀ x ∈ closedSquare ρ,
          (Real.sqrt d.scale)⁻¹ • x ∈ closedBall (0 : E2) d.matchingRadius) ∧
        (d.flatten ∘ s.leaf ∘ s.chart) '' closedSquare ρ ⊆ U ∧
        ∀ u, EqOn (planarHeightMap Φ u) id U

private theorem transfer_one_lower_end
    {v : E3} {g : S2 → E3} {C : Set S2} {p : S2} {B B' : Set Real}
    (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q => inner Real v (g q)))
    (hunique : ∀ q ∈ C,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (g q)) q = 0 → q = p)
    (A : AnnularEndFamily v g B C) (A' : AnnularEndFamily v g B' C)
    (hlow : A.lowerCut < inner Real v (g p))
    (hupp : inner Real v (g p) < A.upperCut)
    (hlow' : A'.lowerCut < inner Real v (g p))
    (hupp' : inner Real v (g p) < A'.upperCut)
    (hcount : Nat.card A.LowerCutIndex = 1) : Nat.card A'.LowerCutIndex = 1 := by
  let h : S2 → Real := fun q => inner Real v (g q)
  have hregular {B'' : Set Real} (A'' : AnnularEndFamily v g B'' C)
      (hupper : h p < A''.upperCut) {b : Real} (hb : b < h p)
      (q : S2) (hq : h q ∈ Icc A''.lowerCut b) :
      mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0 := by
    intro hc
    have hqcore : q ∈ C := A''.physical_middle_band_subset_core
      ⟨hq.1, by change h q ≤ A''.upperCut; linarith [hq.2]⟩
    have hqp := hunique q hqcore hc
    subst q
    exact hb.not_ge hq.2
  apply A'.card_lowerCutIndex_eq_one_of_isConnected
  have hbottom := lower_level_connected_of_one_annular_end A hcount
  rcases le_total A.lowerCut A'.lowerCut with hle | hle
  · exact connected_top_of_regular_band hh hle (hregular A hupp hlow') hbottom
  · have hnreg (q : S2) (hq : -h q ∈ Icc (-A.lowerCut) (-A'.lowerCut)) :
        mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => -h q) q ≠ 0 := by
      change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) q ≠ 0
      rw [mfderiv_neg]
      exact neg_ne_zero.mpr (hregular A' hupp' hlow q
        ⟨by linarith [hq.2], by linarith [hq.1]⟩)
    have hn := connected_top_of_regular_band hh.neg (neg_le_neg hle) hnreg
      (show IsConnected ((fun q => -h q) ⁻¹' {-A.lowerCut}) by
        simpa only [preimage, mem_singleton_iff, neg_inj] using hbottom)
    simpa only [preimage, mem_singleton_iff, neg_inj] using hn

theorem exists_original_or_reflected_planar_family
    {f : S2 → E3} {p : S2} (s : TerminalInputData f p) :
    FullPlanarFamily s ∨
      ∃ s' : TerminalInputData s.reduction.reflectedOriginal p,
        s'.reduction.v = s.reduction.v ∧ s'.reduction.D = s.reduction.D ∧
        s'.leaf = heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property) ∘ s.leaf ∧
        s'.path.core = s.path.core ∧ s'.chart = reflectedMorseChart s.chart ∧
        (∀ q, s'.reduction.D (s.reduction.reflectedOriginal q) =
          heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property)
            (s.reduction.D (f q))) ∧ FullPlanarFamily s' := by
  have alternative {f' : S2 → E3} (t : TerminalInputData f' p) :
      (∃ d : TerminalSaddleGeometry t.reduction t.path p t.chart,
        Nat.card d.ends.LowerCutIndex = 1) ∨ FullPlanarFamily t :=
    exists_terminal_labeled_planar_family_or_one_lower_end
      t.reduction t.leaf_mem t.path t.protects t.preserves_caps t.point_interior
      t.critical t.unique t.chart t.chart_zero t.chart_center t.chart_smooth
      t.chart_inverse_smooth t.form
  rcases alternative s with ⟨d, hd⟩ | hfamily
  · obtain ⟨s', hv', hD', hg', hcore', he', hinit⟩ := s.exists_reflected
    rcases alternative s' with ⟨d', hd'⟩ | hfamily'
    · exfalso
      let hv : ‖(s.reduction.v : E3)‖ = 1 :=
        mem_sphere_zero_iff_norm.mp s.reduction.v.property
      obtain ⟨R, _, _, _, hRl, hRu, _, _, _, hRcount, _⟩ :=
        d.ends.exists_reflectedProtected hv
      have hRl' : R.lowerCut <
          inner Real (s.reduction.v : E3) ((heightReflection hv ∘ s.leaf) p) := by
        rw [hRl, d.upperCut_eq]
        simp only [comp_apply, inner_heightReflection]
        linarith [d.eta_pos]
      have hRu' : inner Real (s.reduction.v : E3)
          ((heightReflection hv ∘ s.leaf) p) < R.upperCut := by
        rw [hRu, d.lowerCut_eq]
        simp only [comp_apply, inner_heightReflection]
        linarith [d.eta_pos]
      have hreflected : ∃ (B : Set Real)
          (R' : AnnularEndFamily (s'.reduction.v : E3) s'.leaf B s'.path.core),
          R'.lowerCut < inner Real (s'.reduction.v : E3) (s'.leaf p) ∧
          inner Real (s'.reduction.v : E3) (s'.leaf p) < R'.upperCut ∧
          Nat.card R'.LowerCutIndex = Nat.card d.ends.UpperCutIndex := by
        rw [hcore', hg', hv']
        exact ⟨_, R, hRl', hRu', hRcount⟩
      obtain ⟨B, R', hRl'', hRu'', hRcount'⟩ := hreflected
      have hdlo : d'.ends.lowerCut < inner Real (s'.reduction.v : E3) (s'.leaf p) := by
        rw [d'.lowerCut_eq]
        linarith [d'.eta_pos]
      have hdhi : inner Real (s'.reduction.v : E3) (s'.leaf p) < d'.ends.upperCut := by
        rw [d'.upperCut_eq]
        linarith [d'.eta_pos]
      have hRone := transfer_one_lower_end
        ((innerSL Real (s'.reduction.v : E3)).contMDiff.comp
          (s'.reduction.tree.embedding_of_mem_leaves s'.leaf_mem).contMDiff)
        s'.unique d'.ends R' hdlo hdhi hRl'' hRu'' hd'
      have hupper : Nat.card d.ends.UpperCutIndex = 1 := hRcount'.symm.trans hRone
      have hthree : Nat.card d.ends.EndIndex = 3 := by
        rw [← Nat.card_congr d.labels]
        simp
      rw [d.ends.card_endIndex_eq_sum, hd, hupper] at hthree
      norm_num at hthree
    · exact Or.inr ⟨s', hv', hD', hg', hcore', he', hinit, hfamily'⟩
  · exact Or.inl hfamily

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar

end

end M38Schoenflies

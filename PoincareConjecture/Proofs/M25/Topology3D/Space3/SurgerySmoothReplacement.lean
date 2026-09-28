import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryOverlap
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight















set_option autoImplicit false

open Set Metric Topology
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D



theorem surgeryNorthMap_mfderiv_injective
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hi : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target)
    {q : UnitTwoSphere} (hq : q ∈ (surgeryNorthChart R e).source) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3)
      (fun p : UnitTwoSphere => ψ (surgeryNorthChart R e p, 0)) q) := by
  have hcentral := (collar_central_contMDiff ψ hψ).mdifferentiable (by simp)
  have hN := (surgeryNorthChart_contMDiffOn R e he).contMDiffAt
    ((surgeryNorthChart R e).open_source.mem_nhds hq)
  change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3)
    ((fun p : UnitTwoSphere => ψ (p, 0)) ∘ surgeryNorthChart R e) q)
  rw [mfderiv_comp q (hcentral _) (hN.mdifferentiableAt (by simp))]
  exact (collar_central_mfderiv_injective ψ hψ _).comp
    (surgeryNorthChart_mfderiv_injective R e he hi hq)




theorem surgeryReplacementMap_smooth_closedEmbedding
    (a : ℝ → ℝ) (b : E2 → ℝ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (ha0 : ∀ z, a z ≠ 0) (hb0 : ∀ x, b x ≠ 0)
    (hapos : ∀ z, 0 < a z)
    (habound : ∀ z, |z| < 1 → a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbpos : ∀ x, 0 < b x)
    (hanear : ∀ z, |z| ≤ 1 / 4 → a z = (Real.sqrt (1 - z ^ 2))⁻¹)
    (hbfar : ∀ x, 1 / 2 ≤ ‖x‖ → b x = 1)
    (ψ : UnitTwoSphere × ℝ → E3) (hψ : IsCollarEmbedding ψ)
    (u : UnitTwoSphere) (t : ℝ) (D : RegularSurgeryData ψ u t)
    (R : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (e : OpenPartialHomeomorph E2 UnitTwoSphere)
    (he : closedBall 0 1 ⊆ e.source)
    (hem : ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target)
    (sigma : ℝ) (hsigma : |sigma| = 1) {delta r k l M : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hrdelta : 1 - r < delta) (hk : 0 < k)
    (hcwidth : k * (1 - r) < D.width)
    (hRball : R '' closedBall 0 1 = closedBall 0 r)
    (hR : ∀ x ∈ sphere (0 : E2) 1, R x = r • x)
    (hRnear : ∀ᶠ w in nhdsSet (sphere (0 : E2) 1),
      R w = surgeryMatchingRadius r (l / k) ‖w‖ • NormedSpace.normalize w)
    (hnear : ∀ x : E2, |‖x‖ - 1| < delta →
      x ∈ e.source ∧ e x = D.sourceCollar
        (circleDirection x, sigma * (k * (1 - ‖x‖))))
    (hl : 0 < l) (hlM : l * M < k * (1 - r) / 4)
    (hM : ∀ q : UnitTwoSphere, |(surgeryCapModel a b ha hb ha0 hb0 q).2| ≤ M) :
    let j := surgeryReplacementMap a b ha hb ha0 hb0 ψ R e D.tube t sigma r k l
    ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j ∧
      (∀ q, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E3) j q)) ∧
      IsClosedEmbedding j := by
  let N := surgeryNorthChart R e
  let f : UnitTwoSphere → E3 := fun q => ψ (N q, 0)
  let g := surgeryCapMap a b ha hb ha0 hb0 D.tube t sigma (k * (1 - r)) l
  let height : UnitTwoSphere → ℝ := fun q => (heightCoordinates (q : E3)).2
  have hh : Continuous height :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  obtain ⟨d, hd, hoverlap⟩ := exists_surgery_replacement_overlap a b ha hb ha0 hb0
    hanear hbfar ψ u t D R e sigma hsigma hr hr1 hrdelta hk hcwidth hRnear hnear
  obtain ⟨v, hv, hupper⟩ := exists_uniform_upper_level_band height hh N.open_source
    (surgeryNorthChart_contains_hemisphere R e he hr1.le hRball)
  let eta := min d v
  have heta : 0 < eta := lt_min hd hv
  have heq (q : UnitTwoSphere) (hq : |height q| < eta) : f q = g q :=
    (hoverlap q (hq.trans_le (min_le_left d v))).2
  have hsource (q : UnitTwoSphere) (hq : -eta < height q) : q ∈ N.source := by
    apply hupper
    have hm : eta ≤ v := min_le_right d v
    linarith
  have hfm : ContMDiffOn (𝓡 2) 𝓘(ℝ, E3) ∞ f N.source :=
    (collar_central_contMDiff ψ hψ).comp_contMDiffOn
      (surgeryNorthChart_contMDiffOn R e hem)
  have hgm : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ g :=
    surgeryCapMap_contMDiff a b ha hb ha0 hb0 hapos habound
      D.tube D.tube_source D.tube_smooth t sigma (k * (1 - r)) l
  have hcont : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ (levelPaste height f g) :=
    levelPaste_contMDiff height hh f g heta heq
      (hfm.mono (fun q hq => hsource q hq)) hgm.contMDiffOn
  have hsigma0 : sigma ≠ 0 := by
    intro hz
    simp [hz] at hsigma
  have hderiv : ∀ q, Function.Injective
      (mfderiv (𝓡 2) 𝓘(ℝ, E3) (levelPaste height f g) q) := by
    apply levelPaste_mfderiv_injective height hh f g heta heq
    · intro q hq
      exact surgeryNorthMap_mfderiv_injective ψ hψ R e hem hei (hsource q hq)
    · intro q _
      exact surgeryCapMap_mfderiv_injective a b ha hb ha0 hb0 hapos habound
        D.tube D.tube_source D.tube_smooth D.tube_inverse
        t sigma (k * (1 - r)) l hsigma0 hl.ne' q
  have hinj : Function.Injective (levelPaste height f g) :=
    surgeryReplacementMap_injective a b ha hb ha0 hb0 hapos habound hbpos hanear hbfar
      ψ hψ u t D R e he sigma hsigma hr hr1 hrdelta hk hcwidth hRball hR hnear hl hlM hM
  exact ⟨hcont, hderiv, hcont.continuous.isClosedEmbedding hinj⟩

end PoincareConjecture.M25.Topology3D

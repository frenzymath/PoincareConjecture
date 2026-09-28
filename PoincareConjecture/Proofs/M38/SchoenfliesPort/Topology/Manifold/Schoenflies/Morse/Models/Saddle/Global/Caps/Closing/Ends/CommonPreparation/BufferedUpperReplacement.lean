import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Ends.CommonPreparation.LowerReplacement







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

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

open SphereSurgeryCoreCap Poincare.Geometry.Euclidean _root_.Poincare.Geometry.Manifold

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "IP" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private def reverseTime : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞ where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  contMDiff_toFun := contMDiff_id.neg
  contMDiff_invFun := contMDiff_id.neg

set_option maxHeartbeats 1000000 in



theorem exists_buffered_relative_upper_end_replacement_of_surface_germ
    {v : E3} {g f : S2 → E3} {Z : Set Real}
    {D : SphereSurgeryCoreCap v g Z} {C₀ : Set S2} {h : S2 → Real} {a b : Real}
    (A : UpperAnnularEnd D C₀ h a b)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (hDb : D.center ≤ b) (haD : a < D.center)
    (hgerm : ∀ p ∈ C₀, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (d : OpenPartialHomeomorph E2 S2) (hds : closedBall 0 1 ⊆ d.source)
    {p : S2} (hp : p ∈ d '' closedBall 0 1)
    (hpa : a < inner Real v (f p))
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, inner Real v (f (d x)) = a)
    (hunique : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) x = 0 → x = p)
    (seed : S2)
    (hcomponent : d '' closedBall 0 1 =
      closure (connectedComponentIn ((fun q => inner Real v (f q)) ⁻¹' Ioi a) seed))
    (hregular : ∀ q, inner Real v (f q) = a →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) q ≠ 0)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (hform : ∀ x ∈ e.source, inner Real v (f (e x)) = inner Real v (f p) - ‖x‖ ^ 2)
    (T : OpenPartialHomeomorph (S1 × Real) S2)
    (hT : ContMDiffOn IP (𝓡 2) ∞ T T.source)
    (hTi : ContMDiffOn (𝓡 2) IP ∞ T.symm T.target)
    {ε : Real} (hε : 0 < ε)
    (hTs : univ ×ˢ Icc (a - ε) (a + ε) ⊆ T.source)
    (hTh : ∀ q z, z ∈ Icc (a - ε) (a + ε) → inner Real v (f (T (q, z))) = z)
    (hTc : range (fun q : S1 => T (q, a)) = d '' sphere (0 : E2) 1)
    (hTpos : ∀ q z, z ∈ Ioo a (a + ε) → T (q, z) ∈ d '' ball (0 : E2) 1)
    (hrim : range (fun q : S1 => g (A.chart (q, a))) =
      range (fun q : S1 => f (T (q, a))))
    {U : Set E3} (hU : IsOpen U)
    (hrimU : range (fun q : S1 => g (A.chart (q, a))) ⊆ U)
    (hsurface : range g ∩ U = range f ∩ U) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ y ∉ K, F y = y) ∧ (∃ η : Real, 0 < η ∧ EqOn F id {y | inner Real v y ≤ a + η}) ∧
        F '' (g '' A.cappedRegion a) = f '' (d '' closedBall 0 1) := by
  let J := heightReflection D.unit_v
  let g' : S2 → E3 := J ∘ g
  let f' : S2 → E3 := J ∘ f
  have hemb (k : S2 → E3) (hk : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ k) :
      _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (J ∘ k) := by
    apply isSmoothEmbedding_of_injective_mfderiv (J.contMDiff.comp hk.contMDiff)
      (J.injective.comp hk.isEmbedding.injective)
    intro q
    rw [mfderiv_comp q (J.contMDiff.mdifferentiable (by simp) _)
      (hk.contMDiff.mdifferentiable (by simp) _)]
    exact (J.mfderivToContinuousLinearEquiv (by simp) (k q)).injective.comp
      (injective_mfderiv_sphere_embedding hk q)
  have hgerm' : ∀ p ∈ C₀,
      (fun q => -h q) =ᶠ[𝓝 p] (fun q => inner Real v (g' q)) := by
    intro p hp
    filter_upwards [hgerm p hp] with q hq
    change -h q = inner Real v (heightReflection D.unit_v (g q))
    rw [inner_heightReflection, hq]
  have hheight (q : S2) : inner Real v (f' q) = -inner Real v (f q) :=
    inner_heightReflection D.unit_v _
  have hfun : (fun q => inner Real v (f' q)) = -(fun q => inner Real v (f q)) :=
    funext hheight
  have hunique' : ∀ x ∈ d '' closedBall 0 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f' q)) x = 0 → x = p := by
    intro x hx hc
    rw [hfun, mfderiv_neg, neg_eq_zero] at hc
    exact hunique x hx hc
  have hcomponent' : d '' closedBall 0 1 =
      closure (connectedComponentIn ((fun q => inner Real v (f' q)) ⁻¹' Iio (-a)) seed) := by
    have heq : ((fun q => inner Real v (f' q)) ⁻¹' Iio (-a)) =
        ((fun q => inner Real v (f q)) ⁻¹' Ioi a) := by
      ext q
      simp only [mem_preimage, mem_Iio, mem_Ioi, hheight, neg_lt_neg_iff]
    rw [heq]
    exact hcomponent
  have hregular' : ∀ q, inner Real v (f' q) = -a →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f' q)) q ≠ 0 := by
    intro q hq
    rw [hfun, mfderiv_neg, neg_ne_zero]
    apply hregular q
    simpa only [hheight, neg_inj] using hq
  let Q := (Diffeomorph.refl (𝓡 1) S1 (n := ∞)).prodCongr reverseTime
  let P₀ : PartialDiffeomorph IP (𝓡 2) (S1 × Real) S2 ∞ :=
    { T with contMDiffOn_toFun := hT, contMDiffOn_invFun := hTi }
  let P := Q.toPartialDiffeomorph.trans P₀
  let T' := P.toOpenPartialHomeomorph
  have hchart (q : S1) (z : Real) : T' (q, z) = T (q, -z) := rfl
  have hTs' : univ ×ˢ Icc (-a - ε) (-a + ε) ⊆ T'.source := by
    rintro ⟨q, z⟩ ⟨_, hz⟩
    change (q, z) ∈ univ ∧ (q, -z) ∈ T.source
    exact ⟨mem_univ _, hTs ⟨mem_univ _, by linarith [hz.2], by linarith [hz.1]⟩⟩
  have hTh' (q : S1) (z : Real) (hz : z ∈ Icc (-a - ε) (-a + ε)) :
      inner Real v (f' (T' (q, z))) = z := by
    rw [hheight, hchart, hTh q (-z) ⟨by linarith [hz.2], by linarith [hz.1]⟩, neg_neg]
  have hTc' : range (fun q : S1 => T' (q, -a)) = d '' sphere (0 : E2) 1 := by
    simpa only [hchart, neg_neg] using hTc
  have hTneg' (q : S1) (z : Real) (hz : z ∈ Ioo (-a - ε) (-a)) :
      T' (q, z) ∈ d '' ball (0 : E2) 1 := by
    rw [hchart]
    exact hTpos q (-z) ⟨by linarith [hz.2], by linarith [hz.1]⟩
  have hrim' : range (fun q : S1 => g' (A.reflected.chart (q, -a))) =
      range (fun q : S1 => f' (T' (q, -a))) := by
    have hh := congrArg (fun S : Set E3 => J '' S) hrim
    simpa only [g', f', Function.comp_apply, hchart, neg_neg, ← A.chart_apply,
      ← range_comp, Function.comp_def] using hh
  have hrimU' : range (fun q : S1 => g' (A.reflected.chart (q, -a))) ⊆ J '' U := by
    rintro _ ⟨q, rfl⟩
    exact mem_image_of_mem J (hrimU ⟨q, congrArg g (A.chart_apply q a)⟩)
  have hsurface' : range g' ∩ (J '' U) = range f' ∩ (J '' U) := by
    have hJi : Injective (J : E3 → E3) := J.injective
    rw [show range g' = J '' range g from range_comp _ _,
      show range f' = J '' range f from range_comp _ _,
      ← image_inter hJi, ← image_inter hJi, hsurface]
  obtain ⟨K, hK, F₀, hfix, ⟨η, hη, hhalf⟩, himage⟩ :=
    exists_buffered_relative_lower_end_replacement_of_surface_germ A.reflected (hemb g hg)
      (neg_le_neg hDb) (neg_lt_neg haD) hgerm' (hemb f hf) d hds hp
      (by change inner Real v (f' p) < -a; rw [hheight]; exact neg_lt_neg hpa)
      (fun x hx => by change inner Real v (f' (d x)) = -a; rw [hheight, hboundary x hx])
      hunique' seed hcomponent' hregular' e he0 hep he hei
      (fun x hx => by
        change inner Real v (f' (e x)) = inner Real v (f' p) + ‖x‖ ^ 2
        rw [hheight, hform x hx, hheight]
        ring)
      T' P.contMDiffOn P.symm.contMDiffOn hε hTs' hTh' hTc' hTneg' hrim'
      (J.toHomeomorph.isOpenMap U hU) hrimU' hsurface'
  let F := (J.trans F₀).trans J
  refine ⟨J '' K, hK.image J.contMDiff.continuous, F, ?_, ?_, ?_⟩
  · intro y hy
    have hnot : J y ∉ K := fun hh => hy
      ⟨J y, hh, heightReflection_heightReflection D.unit_v y⟩
    change J (F₀ (J y)) = y
    rw [hfix _ hnot]
    exact heightReflection_heightReflection D.unit_v y
  · refine ⟨η, hη, ?_⟩
    intro y hy
    have hj : -a - η ≤ inner Real v (J y) := by
      change -a - η ≤ inner Real v (heightReflection D.unit_v y)
      rw [inner_heightReflection]
      change inner Real v y ≤ a + η at hy
      linarith
    change J (F₀ (J y)) = y
    rw [hhalf hj]
    exact heightReflection_heightReflection D.unit_v y
  · have hFimage : F '' (g '' A.cappedRegion a) =
        J '' (F₀ '' (g' '' A.reflected.cappedRegion (-a))) := by
      rw [← A.cappedRegion_eq_reflected a]
      simp only [F, Diffeomorph.coe_trans, image_comp, g']
    change F₀ '' (g' '' A.reflected.cappedRegion (-a)) = f' '' (d '' closedBall 0 1) at himage
    rw [hFimage, himage, image_image]
    simp only [f', Function.comp_apply, J, heightReflection_heightReflection]

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

end

end M38Schoenflies

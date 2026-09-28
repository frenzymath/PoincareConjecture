import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.LowerAnnulus
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneBoundary.Reflection



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

private def negateTime : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞ where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  contMDiff_toFun := contMDiff_id.neg
  contMDiff_invFun := contMDiff_id.neg

variable {v : E3} {g : S2 → E3} {B : Set Real}



theorem exists_upper_annular_end
    (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C) (hclosed : IsClosed C)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    {a b : Real} (hab : a < b)
    (hupper : ∀ p ∈ C, h p ≤ b)
    (hless : ∃ p ∈ C, h p < a)
    (hregular : ∀ p, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (D : SphereSurgeryCoreCap v g B) (hD : D ∈ L) (haD : a < D.center) :
    0 < D.scale ∧
    ∃ δ : Real, 0 < δ ∧ ∃ F : OpenPartialHomeomorph (S1 × Real) S2,
      F.source = univ ×ˢ Ioo (a - δ) (b + δ) ∧
      ContMDiffOn Iprod (𝓡 2) ∞ F F.source ∧
      ContMDiffOn (𝓡 2) Iprod ∞ F.symm F.target ∧
      (∀ q t, t ∈ Ioo (a - δ) (b + δ) → h (F (q, t)) = t) ∧
      range (fun q : S1 => F (q, D.center)) = D.chart '' sphere (0 : E2) 1 ∧
      F '' (univ ×ˢ Icc a D.center) ⊆ C ∧
      F '' (univ ×ˢ Ioo a D.center) ⊆ interior C ∧
      (∀ q t, t ∈ Icc a D.center → inner Real v (g (F (q, t))) = t) ∧
      ∀ p ∈ D.chart '' sphere (0 : E2) 1,
        F '' (univ ×ˢ Icc a b) = connectedComponentIn (h ⁻¹' Icc a b) p := by
  let R := heightReflection D.unit_v
  let gr : S2 → E3 := fun p => R (g p)
  let LR : List (SphereSurgeryCoreCap v gr ∅) := L.map (fun E => E.reflected)
  have hpairR : LR.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) := by
    rw [show LR = L.map (fun E => E.reflected) from rfl, List.pairwise_map]
    exact hpair
  have hcoreR : C = (⋃ E ∈ LR, E.chart '' ball 0 1)ᶜ := by
    rw [hcore]
    congr 1
    ext p
    simp only [mem_iUnion, LR, List.mem_map]
    constructor
    · rintro ⟨E, hE, hpE⟩
      exact ⟨E.reflected, ⟨E, hE, rfl⟩, hpE⟩
    · rintro ⟨_, ⟨E, hE, rfl⟩, hpE⟩
      exact ⟨E, hE, hpE⟩
  have hgermR : ∀ p ∈ C, -h =ᶠ[𝓝 p] (fun q => inner Real v (gr q)) := by
    intro p hp
    filter_upwards [hgerm p hp] with q hq
    change -h q = inner Real v (heightReflection _ (g q))
    rw [inner_heightReflection, hq]
  have hregR : ∀ p, (-h) p ∈ Icc (-b) (-a) →
      mfderiv (𝓡 2) 𝓘(Real, Real) (-h) p ≠ 0 := by
    intro p hp hc
    change -h p ∈ Icc (-b) (-a) at hp
    have hp' : h p ∈ Icc a b := ⟨by linarith [hp.2], by linarith [hp.1]⟩
    exact hregular p hp' (by simpa only [mfderiv_neg, neg_eq_zero] using hc)
  obtain ⟨hs, δ, hδ, G, hGs, hG, hGi, hheight, hcircle, hretained, hinterior,
      hactual, hcomponent⟩ := exists_lower_annular_end LR hpairR hcoreR hC hclosed hh.neg
    hgermR (neg_lt_neg hab) (fun p hp => neg_le_neg (hupper p hp))
    (by obtain ⟨p, hp, hph⟩ := hless; exact ⟨p, hp, neg_lt_neg hph⟩)
    hregR D.reflected (List.mem_map.mpr ⟨D, hD, rfl⟩) (neg_lt_neg haD)
  let Q := (Diffeomorph.refl (𝓡 1) S1 (n := ∞)).prodCongr negateTime
  let GG : PartialDiffeomorph Iprod (𝓡 2) (S1 × Real) S2 ∞ :=
    { G with contMDiffOn_toFun := hG, contMDiffOn_invFun := hGi }
  let FF := Q.toPartialDiffeomorph.trans GG
  let F := FF.toOpenPartialHomeomorph
  have hformula (q : S1) (t : Real) : F (q, t) = G (q, -t) := rfl
  have hFs : F.source = univ ×ˢ Ioo (a - δ) (b + δ) := by
    ext z
    change (z ∈ univ ∧ (z.1, -z.2) ∈ G.source) ↔ _
    rw [hGs]
    simp only [mem_univ, mem_prod, mem_Ioo, true_and]
    constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
  have hclosedImage (l u : Real) : F '' (univ ×ˢ Icc l u) =
      G '' (univ ×ˢ Icc (-u) (-l)) := by
    ext p
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      exact ⟨(q, -t), ⟨mem_univ _, neg_le_neg ht.2, neg_le_neg ht.1⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      refine ⟨(q, -t), ⟨mem_univ _, by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      simp only [hformula, neg_neg]
  have hopenImage : F '' (univ ×ˢ Ioo a D.center) =
      G '' (univ ×ˢ Ioo (-D.center) (-a)) := by
    ext p
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      exact ⟨(q, -t), ⟨mem_univ _, neg_lt_neg ht.2, neg_lt_neg ht.1⟩, rfl⟩
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      refine ⟨(q, -t), ⟨mem_univ _, by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      simp only [hformula, neg_neg]
  refine ⟨by change -D.scale < 0 at hs; linarith, δ, hδ, F, hFs,
    FF.contMDiffOn, FF.symm.contMDiffOn, ?_, hcircle,
    (hclosedImage a D.center) ▸ hretained, hopenImage ▸ hinterior, ?_, ?_⟩
  · intro q t ht
    have hqt := hheight q (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    change -h (G (q, -t)) = -t at hqt
    rw [hformula]
    linarith
  · intro q t ht
    have hqt := hactual q (-t) ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
    change inner Real v (heightReflection _ (g (G (q, -t)))) = -t at hqt
    rw [inner_heightReflection] at hqt
    rw [hformula]
    linarith
  · intro p hp
    have hset : (fun q => -h q) ⁻¹' Icc (-b) (-a) = h ⁻¹' Icc a b := by
      ext q
      change (-b ≤ -h q ∧ -h q ≤ -a) ↔ (a ≤ h q ∧ h q ≤ b)
      constructor <;> intro hq <;> constructor <;> linarith [hq.1, hq.2]
    rw [hclosedImage, hcomponent p hp, hset]

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

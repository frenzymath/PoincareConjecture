import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.Coverage

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology
open Poincare.Geometry.Euclidean

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1
local notation "Iprod" => ModelWithCorners.prod (𝓡 1) 𝓘(Real, Real)

variable {v : E3} {g : S2 → E3} {B : Set Real}

structure UpperAnnularEnd (D : SphereSurgeryCoreCap v g B)
    (C : Set S2) (h : S2 → Real) (a b : Real) where
  reflected : LowerAnnularEnd D.reflected C (fun p => -h p) (-b) (-a)

namespace UpperAnnularEnd

variable {D : SphereSurgeryCoreCap v g B} {C : Set S2} {h : S2 → Real} {a b : Real}

private def negateTime : Diffeomorph 𝓘(Real, Real) 𝓘(Real, Real) Real Real ∞ where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  contMDiff_toFun := contMDiff_id.neg
  contMDiff_invFun := contMDiff_id.neg

private def partialChart (A : UpperAnnularEnd D C h a b) :
    PartialDiffeomorph Iprod (𝓡 2) (S1 × Real) S2 ∞ :=
  ((Diffeomorph.refl (𝓡 1) S1 (n := ∞)).prodCongr negateTime).toPartialDiffeomorph.trans
    { A.reflected.chart with
      contMDiffOn_toFun := A.reflected.smooth
      contMDiffOn_invFun := A.reflected.symm_smooth }

def chart (A : UpperAnnularEnd D C h a b) : OpenPartialHomeomorph (S1 × Real) S2 :=
  A.partialChart.toOpenPartialHomeomorph

def region (A : UpperAnnularEnd D C h a b) : Set S2 := A.reflected.region

theorem chart_apply (A : UpperAnnularEnd D C h a b) (q : S1) (t : Real) :
    A.chart (q, t) = A.reflected.chart (q, -t) := rfl

theorem source (A : UpperAnnularEnd D C h a b) :
    A.chart.source = univ ×ˢ Ioo (a - A.reflected.delta) (b + A.reflected.delta) := by
  ext z
  change (z ∈ univ ∧ (z.1, -z.2) ∈ A.reflected.chart.source) ↔ _
  rw [A.reflected.source]
  simp only [mem_univ, mem_prod, mem_Ioo, true_and]
  constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]

theorem smooth (A : UpperAnnularEnd D C h a b) :
    ContMDiffOn Iprod (𝓡 2) ∞ A.chart A.chart.source := A.partialChart.contMDiffOn

theorem symm_smooth (A : UpperAnnularEnd D C h a b) :
    ContMDiffOn (𝓡 2) Iprod ∞ A.chart.symm A.chart.target := A.partialChart.symm.contMDiffOn

theorem height (A : UpperAnnularEnd D C h a b) (q : S1) (t : Real)
    (ht : t ∈ Ioo (a - A.reflected.delta) (b + A.reflected.delta)) :
    h (A.chart (q, t)) = t := by
  have hh := A.reflected.height q (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  change -h (A.chart (q, t)) = -t at hh
  linarith

theorem image_closed_strip (A : UpperAnnularEnd D C h a b) (l u : Real) :
    A.chart '' (univ ×ˢ Icc l u) = A.reflected.chart '' (univ ×ˢ Icc (-u) (-l)) := by
  ext p
  constructor
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    exact ⟨(q, -t), ⟨mem_univ _, neg_le_neg ht.2, neg_le_neg ht.1⟩, rfl⟩
  · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
    refine ⟨(q, -t), ⟨mem_univ _, by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    simp only [chart_apply, neg_neg]

theorem region_eq_image (A : UpperAnnularEnd D C h a b) :
    A.region = A.chart '' (univ ×ˢ Icc a D.center) := by
  rw [A.image_closed_strip]
  rfl

theorem retained (A : UpperAnnularEnd D C h a b) : A.region ⊆ C := A.reflected.retained

theorem interior (A : UpperAnnularEnd D C h a b) :
    A.chart '' (univ ×ˢ Ioo a D.center) ⊆ interior C := by
  rintro p ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
  exact A.reflected.interior (mem_image_of_mem _
    ⟨mem_univ _, neg_lt_neg ht.2, neg_lt_neg ht.1⟩)

theorem boundary (A : UpperAnnularEnd D C h a b) :
    range (fun q : S1 => A.chart (q, D.center)) = D.chart '' sphere (0 : E2) 1 :=
  A.reflected.boundary

theorem actual_height (A : UpperAnnularEnd D C h a b) (q : S1) (t : Real)
    (ht : t ∈ Icc a D.center) : inner Real v (g (A.chart (q, t))) = t := by
  have hh := A.reflected.actual_height q (-t) ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
  change inner Real v (heightReflection D.unit_v (g (A.chart (q, t)))) = -t at hh
  rw [inner_heightReflection] at hh
  linarith

theorem scale_pos (A : UpperAnnularEnd D C h a b) : 0 < D.scale := by
  have hs := A.reflected.scale_neg
  change -D.scale < 0 at hs
  linarith

end UpperAnnularEnd

theorem exists_upper_annular_end_family
    (hv : ‖v‖ = 1) (L : List (SphereSurgeryCoreCap v g B))
    (hpair : L.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)))
    {C : Set S2} (hcore : C = (⋃ D ∈ L, D.chart '' ball 0 1)ᶜ)
    (hC : IsPreconnected C) (hclosed : IsClosed C)
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (hgerm : ∀ p ∈ C, h =ᶠ[𝓝 p] (fun q => inner Real v (g q)))
    {a b : Real} (hab : a < b)
    (hupper : ∀ p ∈ C, h p < b) (hless : ∃ p ∈ C, h p < a)
    (hregular : ∀ p, h p ∈ Icc a b → mfderiv (𝓡 2) 𝓘(Real, Real) h p ≠ 0)
    (hcut : ∀ D ∈ L, D.center ≠ a) :
    ∃ ends : ∀ D ∈ L, a < D.center → UpperAnnularEnd D C h a b,
      (∀ D hD haD E hE haE, D ≠ E →
        Disjoint (ends D hD haD).region (ends E hE haE).region) ∧
      (⋃ D, ⋃ hD : D ∈ L, ⋃ haD : a < D.center, (ends D hD haD).region) =
        C ∩ h ⁻¹' Ici a := by
  classical
  let gr : S2 → E3 := fun p => heightReflection hv (g p)
  let LR : List (SphereSurgeryCoreCap v gr ∅) := L.map (fun D => D.reflected)
  have hpairR : LR.Pairwise (fun D E => Disjoint
      (D.chart '' closedBall 0 1) (E.chart '' closedBall 0 1)) := by
    rw [show LR = L.map (fun D => D.reflected) from rfl, List.pairwise_map]
    exact hpair
  have hcoreR : C = (⋃ D ∈ LR, D.chart '' ball 0 1)ᶜ := by
    rw [hcore]
    congr 1
    ext p
    simp only [mem_iUnion, LR, List.mem_map]
    constructor
    · rintro ⟨D, hD, hpD⟩
      exact ⟨D.reflected, ⟨D, hD, rfl⟩, hpD⟩
    · rintro ⟨_, ⟨D, hD, rfl⟩, hpD⟩
      exact ⟨D, hD, hpD⟩
  have hgermR : ∀ p ∈ C, (fun q => -h q) =ᶠ[𝓝 p] (fun q => inner Real v (gr q)) := by
    intro p hp
    filter_upwards [hgerm p hp] with q hq
    simp only [gr, inner_heightReflection, hq]
  have hregularR : ∀ p, -h p ∈ Icc (-b) (-a) →
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => -h q) p ≠ 0 := by
    intro p hp hc
    apply hregular p ⟨by linarith [hp.2], by linarith [hp.1]⟩
    change mfderiv (𝓡 2) 𝓘(Real, Real) (-h) p = 0 at hc
    simpa only [mfderiv_neg, neg_eq_zero] using hc
  have hcutR : ∀ D ∈ LR, D.center ≠ -a := by
    intro D hD
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    intro heq
    exact hcut E hE (neg_injective heq)
  obtain ⟨endsR, hdisjoint, hcover⟩ := exists_lower_annular_end_family LR hpairR hcoreR
    hC hclosed hh.neg hgermR (neg_lt_neg hab) (fun p hp => neg_lt_neg (hupper p hp))
    (by obtain ⟨p, hp, hph⟩ := hless; exact ⟨p, hp, neg_lt_neg hph⟩)
    hregularR hcutR
  let ends : ∀ D ∈ L, a < D.center → UpperAnnularEnd D C h a b :=
    fun D hD haD => ⟨endsR D.reflected (List.mem_map.mpr ⟨D, hD, rfl⟩) (neg_lt_neg haD)⟩
  refine ⟨ends, ?_, ?_⟩
  · intro D hD haD E hE haE hne
    apply hdisjoint
    intro heq
    have hchart : D.chart = E.chart := congrArg (fun J => J.chart) heq
    obtain ⟨p, hp⟩ := D.isConnected_boundary.nonempty
    have hpD := image_mono sphere_subset_closedBall hp
    exact Set.disjoint_left.mp (hpair.forall hD hE hne) hpD (hchart ▸ hpD)
  · ext p
    constructor
    · simp only [mem_iUnion]
      rintro ⟨D, hD, haD, hp⟩
      have hpR : p ∈ C ∩ (fun q => -h q) ⁻¹' Iic (-a) := hcover.subset
        (mem_iUnion_of_mem D.reflected (mem_iUnion_of_mem (List.mem_map.mpr ⟨D, hD, rfl⟩)
          (mem_iUnion_of_mem (neg_lt_neg haD) hp)))
      exact ⟨hpR.1, show a ≤ h p from neg_le_neg_iff.mp (show -h p ≤ -a from hpR.2)⟩
    · rintro ⟨hpC, hpa⟩
      have hpR := hcover.superset (show p ∈ C ∩ (fun q => -h q) ⁻¹' Iic (-a) from
        ⟨hpC, show -h p ≤ -a from neg_le_neg (show a ≤ h p from hpa)⟩)
      simp only [mem_iUnion] at hpR ⊢
      obtain ⟨D, hD, hDa, hpD⟩ := hpR
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
      have haE : a < E.center := neg_lt_neg_iff.mp hDa
      exact ⟨E, hE, haE, hpD⟩

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap

end

end M38Schoenflies

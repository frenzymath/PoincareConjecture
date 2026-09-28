import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.CoreCaps
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Reflection.TerminalInputs
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CutCircles

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar
open SphereSurgeryCoreCap
open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

private def lowerRetarget
    {g' : S2 → E3} {B' : Set Real}
    {D : SphereSurgeryCoreCap v g B} {D' : SphereSurgeryCoreCap v g' B'}
    (hc : D'.chart = D.chart) (hz : D'.center = D.center) (hs : D'.scale = D.scale)
    (hh : ∀ q, inner Real v (g' q) = inner Real v (g q))
    {h : S2 → Real} {a b : Real} (A : LowerAnnularEnd D C h a b) :
    LowerAnnularEnd D' C h a b where
  delta := A.delta
  delta_pos := A.delta_pos
  chart := A.chart
  source := A.source
  smooth := A.smooth
  symm_smooth := A.symm_smooth
  height := A.height
  boundary := by simpa only [hz, hc] using A.boundary
  retained := by simpa only [hz] using A.retained
  interior := by simpa only [hz] using A.interior
  actual_height := by
    intro q t ht
    rw [hh]
    exact A.actual_height q t (hz ▸ ht)
  component := by simpa only [hc] using A.component
  scale_neg := hs ▸ A.scale_neg

private def reflectedUpperToLower {D : SphereSurgeryCoreCap v g B}
    {h : S2 → Real} {a b : Real} (A : UpperAnnularEnd D C h a b) :
    LowerAnnularEnd D.reflectedProtected C (fun q => -h q) (-b) (-a) :=
  lowerRetarget (D := D.reflected) (D' := D.reflectedProtected)
    rfl rfl rfl (fun _ => rfl) A.reflected

private def reflectedLowerToUpper {D : SphereSurgeryCoreCap v g B}
    {h : S2 → Real} {a b : Real} (A : LowerAnnularEnd D C h a b) :
    UpperAnnularEnd D.reflectedProtected C (fun q => -h q) (-b) (-a) where
  reflected := {
    delta := A.delta
    delta_pos := A.delta_pos
    chart := A.chart
    source := by simpa only [neg_neg] using A.source
    smooth := A.smooth
    symm_smooth := A.symm_smooth
    height := by simpa only [neg_neg] using A.height
    boundary := by simpa only [reflected, reflectedProtected, neg_neg] using A.boundary
    retained := by simpa only [reflected, reflectedProtected, neg_neg] using A.retained
    interior := by simpa only [reflected, reflectedProtected, neg_neg] using A.interior
    actual_height := by
      intro q t ht
      simpa only [comp_apply, inner_heightReflection, neg_neg] using
        A.actual_height q t (by simpa only [reflected, reflectedProtected, neg_neg] using ht)
    component := by simpa only [reflected, reflectedProtected, neg_neg] using A.component
    scale_neg := by simpa only [reflected, reflectedProtected, neg_neg] using A.scale_neg }

private theorem reflectedUpperToLower_region {D : SphereSurgeryCoreCap v g B}
    {h : S2 → Real} {a b : Real} (A : UpperAnnularEnd D C h a b) :
    (reflectedUpperToLower A).region = A.region := rfl

private theorem reflectedLowerToUpper_region {D : SphereSurgeryCoreCap v g B}
    {h : S2 → Real} {a b : Real} (A : LowerAnnularEnd D C h a b) :
    (reflectedLowerToUpper A).region = A.region := by
  change A.chart '' (univ ×ˢ Icc (- -D.center) (- -b)) = A.region
  simp only [neg_neg, LowerAnnularEnd.region]

namespace ReflectedEnds

theorem exists_reflected_endCaps (A : AnnularEndFamily v g B C) (hv : ‖v‖ = 1) :
    ∃ R : AnnularEndFamily v (heightReflection hv ∘ g) (Neg.neg '' B) C,
      R.caps = A.caps.map (fun D => D.reflectedProtected) ∧
      R.height = (fun q => -A.height q) ∧
      R.lowerBound = -A.upperBound ∧ R.lowerCut = -A.upperCut ∧
      R.upperCut = -A.lowerCut ∧ R.upperBound = -A.lowerBound ∧
      ∃ e : A.EndIndex ≃ R.EndIndex,
        ∀ i, terminalEndCap R (e i) = terminalEndCap A i := by
  classical
  let LR : List (SphereSurgeryCoreCap v (heightReflection hv ∘ g) (Neg.neg '' B)) :=
    A.caps.map (fun D => D.reflectedProtected)
  have hlower (D) (hD : D ∈ LR) (hz : D.center < -A.upperCut) :
      ∃ L : LowerAnnularEnd D C (fun q => -A.height q) (-A.upperBound) (-A.upperCut),
        ∃ E, ∃ hE : E ∈ A.caps, ∃ hEz : A.upperCut < E.center,
          E.reflectedProtected = D ∧ L.region = (A.upper E hE hEz).region := by
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    have hEz : A.upperCut < E.center := neg_lt_neg_iff.mp hz
    exact ⟨reflectedUpperToLower (A.upper E hE hEz), E, hE, hEz, rfl,
      reflectedUpperToLower_region _⟩
  choose lower hlower using hlower
  have hupper (D) (hD : D ∈ LR) (hz : -A.lowerCut < D.center) :
      ∃ L : UpperAnnularEnd D C (fun q => -A.height q) (-A.lowerCut) (-A.lowerBound),
        ∃ E, ∃ hE : E ∈ A.caps, ∃ hEz : E.center < A.lowerCut,
          E.reflectedProtected = D ∧ L.region = (A.lower E hE hEz).region := by
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    have hEz : E.center < A.lowerCut := neg_lt_neg_iff.mp hz
    exact ⟨reflectedLowerToUpper (A.lower E hE hEz), E, hE, hEz, rfl,
      reflectedLowerToUpper_region _⟩
  choose upper hupper using hupper
  have hloweq (D) (hD : D ∈ A.caps) (hz : A.upperCut < D.center) :
      (lower D.reflectedProtected (List.mem_map.mpr ⟨D, hD, rfl⟩)
        (neg_lt_neg hz)).region = (A.upper D hD hz).region := by
    obtain ⟨E, hE, hEz, heq, hreg⟩ := hlower D.reflectedProtected
      (List.mem_map.mpr ⟨D, hD, rfl⟩) (neg_lt_neg hz)
    have he : E = D := reflectedProtected_injective hv heq
    subst E
    exact hreg
  have hupeq (D) (hD : D ∈ A.caps) (hz : D.center < A.lowerCut) :
      (upper D.reflectedProtected (List.mem_map.mpr ⟨D, hD, rfl⟩)
        (neg_lt_neg hz)).region = (A.lower D hD hz).region := by
    obtain ⟨E, hE, hEz, heq, hreg⟩ := hupper D.reflectedProtected
      (List.mem_map.mpr ⟨D, hD, rfl⟩) (neg_lt_neg hz)
    have he : E = D := reflectedProtected_injective hv heq
    subst E
    exact hreg
  let R : AnnularEndFamily v (heightReflection hv ∘ g) (Neg.neg '' B) C := {
    caps := LR
    caps_disjoint := by
      rw [List.pairwise_map]
      exact A.caps_disjoint
    core_complement := by
      rw [A.core_complement]
      congr 1
      ext q
      simp only [mem_iUnion, LR, List.mem_map]
      constructor
      · rintro ⟨D, hD, hq⟩
        exact ⟨D.reflectedProtected, ⟨D, hD, rfl⟩, hq⟩
      · rintro ⟨_, ⟨D, hD, rfl⟩, hq⟩
        exact ⟨D, hD, hq⟩
    height := fun q => -A.height q
    height_smooth := A.height_smooth.neg
    height_germ := by
      intro q hq
      filter_upwards [A.height_germ q hq] with x hx
      simp only [comp_apply, inner_heightReflection, hx]
    lowerBound := -A.upperBound
    lowerCut := -A.upperCut
    upperCut := -A.lowerCut
    upperBound := -A.lowerBound
    lower_lt := neg_lt_neg A.upper_lt
    cuts_lt := neg_lt_neg A.cuts_lt
    upper_lt := neg_lt_neg A.lower_lt
    core_height_bounds := fun q hq =>
      ⟨neg_lt_neg (A.core_height_bounds q hq).2, neg_lt_neg (A.core_height_bounds q hq).1⟩
    lower := lower
    upper := upper
    lower_disjoint := by
      intro D hD hz E hE hw hne
      obtain ⟨D₀, hD₀, hz₀, rfl, hrD⟩ := hlower D hD hz
      obtain ⟨E₀, hE₀, hw₀, rfl, hrE⟩ := hlower E hE hw
      rw [hrD, hrE]
      exact A.upper_disjoint D₀ hD₀ hz₀ E₀ hE₀ hw₀ (fun heq => hne (congrArg _ heq))
    upper_disjoint := by
      intro D hD hz E hE hw hne
      obtain ⟨D₀, hD₀, hz₀, rfl, hrD⟩ := hupper D hD hz
      obtain ⟨E₀, hE₀, hw₀, rfl, hrE⟩ := hupper E hE hw
      rw [hrD, hrE]
      exact A.lower_disjoint D₀ hD₀ hz₀ E₀ hE₀ hw₀ (fun heq => hne (congrArg _ heq))
    lower_cover := by
      ext q
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_Iic, neg_le_neg_iff]
      constructor
      · rintro ⟨D, hD, hz, hq⟩
        obtain ⟨E, hE, hEz, rfl, hr⟩ := hlower D hD hz
        exact A.upper_cover.subset (mem_iUnion_of_mem E (mem_iUnion_of_mem hE
          (mem_iUnion_of_mem hEz (hr ▸ hq))))
      · intro hq
        obtain ⟨D, hD, hz, hq⟩ := by
          simpa only [mem_iUnion] using A.upper_cover.superset hq
        exact ⟨D.reflectedProtected, List.mem_map.mpr ⟨D, hD, rfl⟩,
          neg_lt_neg hz, (hloweq D hD hz).symm ▸ hq⟩
    upper_cover := by
      ext q
      simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_Ici, neg_le_neg_iff]
      constructor
      · rintro ⟨D, hD, hz, hq⟩
        obtain ⟨E, hE, hEz, rfl, hr⟩ := hupper D hD hz
        exact A.lower_cover.subset (mem_iUnion_of_mem E (mem_iUnion_of_mem hE
          (mem_iUnion_of_mem hEz (hr ▸ hq))))
      · intro hq
        obtain ⟨D, hD, hz, hq⟩ := by
          simpa only [mem_iUnion] using A.lower_cover.superset hq
        exact ⟨D.reflectedProtected, List.mem_map.mpr ⟨D, hD, rfl⟩,
          neg_lt_neg hz, (hupeq D hD hz).symm ▸ hq⟩
    cap_side := by
      intro D hD
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
      rcases A.cap_side E hE with hl | hu
      · exact Or.inr (neg_lt_neg hl)
      · exact Or.inl (neg_lt_neg hu)
    height_germ_on_cap := by
      intro D hD q hq hh
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
      rw [reflectedProtected_normalized_height] at hh
      filter_upwards [A.height_germ_on_cap E hE q hq hh] with x hx
      simp only [comp_apply, inner_heightReflection, hx] }
  let eL : A.UpperCutIndex ≃ R.LowerCutIndex := Equiv.ofBijective
    (fun i => ⟨⟨i.1.1.reflectedProtected, List.mem_map.mpr ⟨i.1.1, i.1.2, rfl⟩⟩,
      neg_lt_neg i.2⟩) (by
      constructor
      · intro i j hij
        apply Subtype.ext
        apply Subtype.ext
        exact reflectedProtected_injective hv (congrArg (fun i => i.1.1) hij)
      · rintro ⟨⟨D, hD⟩, hz⟩
        obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
        refine ⟨⟨⟨E, hE⟩, neg_lt_neg_iff.mp hz⟩, ?_⟩
        rfl)
  let eU : A.LowerCutIndex ≃ R.UpperCutIndex := Equiv.ofBijective
    (fun i => ⟨⟨i.1.1.reflectedProtected, List.mem_map.mpr ⟨i.1.1, i.1.2, rfl⟩⟩,
      neg_lt_neg i.2⟩) (by
      constructor
      · intro i j hij
        apply Subtype.ext
        apply Subtype.ext
        exact reflectedProtected_injective hv (congrArg (fun i => i.1.1) hij)
      · rintro ⟨⟨D, hD⟩, hz⟩
        obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
        refine ⟨⟨⟨E, hE⟩, neg_lt_neg_iff.mp hz⟩, ?_⟩
        rfl)
  let e : A.EndIndex ≃ R.EndIndex :=
    (Equiv.sumCongr eU eL).trans (Equiv.sumComm _ _)
  refine ⟨R, rfl, rfl, rfl, rfl, rfl, rfl, e, ?_⟩
  rintro (i | i)
  · change (upper i.1.1.reflectedProtected _ _).region ∪
        i.1.1.reflectedProtected.chart '' closedBall 0 1 =
      (A.lower i.1.1 i.1.2 i.2).region ∪ i.1.1.chart '' closedBall 0 1
    rw [hupeq]
    rfl
  · change (lower i.1.1.reflectedProtected _ _).region ∪
        i.1.1.reflectedProtected.chart '' closedBall 0 1 =
      (A.upper i.1.1 i.1.2 i.2).region ∪ i.1.1.chart '' closedBall 0 1
    rw [hloweq]
    rfl

theorem exists_back
    {v' : E3} {g' : S2 → E3} {B' : Set Real} {C' : Set S2}
    (A : AnnularEndFamily v' g' B' C') (hv' : ‖v'‖ = 1)
    (hv : v' = v) (hg : heightReflection hv' ∘ g' = g)
    (hB : Neg.neg '' B' = B) (hC : C' = C) :
    ∃ R : AnnularEndFamily v g B C,
      R.lowerCut = -A.upperCut ∧ R.upperCut = -A.lowerCut ∧
      ∃ e : A.EndIndex ≃ R.EndIndex,
        ∀ i, terminalEndCap R (e i) = terminalEndCap A i := by
  subst v
  subst g
  subst B
  subst C
  obtain ⟨R, _, _, _, hl, hu, _, e, he⟩ := exists_reflected_endCaps A hv'
  exact ⟨R, hl, hu, e, he⟩

end ReflectedEnds

open PlaneArcs.Terminal.Reflection

theorem reflected_critical_values {v : E3} (hv : ‖v‖ = 1) (g : S2 → E3) :
    (fun q => inner Real v (heightReflection hv (g q))) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real v (heightReflection hv (g y))) q = 0} =
    Neg.neg '' ((fun q => inner Real v (g q)) ''
      {q | mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real v (g y)) q = 0}) := by
  have hc :
      {q | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y => inner Real v (heightReflection hv (g y))) q = 0} =
      {q | mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real v (g y)) q = 0} :=
    Set.ext (reflected_height_critical_iff hv g)
  rw [hc, image_image]
  exact image_congr (fun q _ => inner_heightReflection hv _)

theorem exists_original_ends
    {f : S2 → E3} {p : S2} (s : TerminalInputData f p)
    (s' : TerminalInputData s.reduction.reflectedOriginal p)
    (hv : s'.reduction.v = s.reduction.v)
    (hleaf : s'.leaf =
      heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property) ∘ s.leaf)
    (hcore : s'.path.core = s.path.core)
    (hinit : ∀ q, s'.reduction.D (s.reduction.reflectedOriginal q) =
      heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property)
        (s.reduction.D (f q)))
    (d : SaddleLevel.TerminalSaddleGeometry s'.reduction s'.path p s'.chart) :
    ∃ A : AnnularEndFamily (s.reduction.v : E3) s.leaf
      ((fun q => inner Real (s.reduction.v : E3) (s.reduction.D (f q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (s.reduction.v : E3) (s.reduction.D (f y))) q = 0})
      s.path.core,
      A.lowerCut = -d.ends.upperCut ∧ A.upperCut = -d.ends.lowerCut ∧
      ∃ e : d.ends.EndIndex ≃ A.EndIndex,
        ∀ i, terminalEndCap A (e i) = SaddleLevel.terminalEndCap d.ends i := by
  let hv' : ‖(s'.reduction.v : E3)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp s'.reduction.v.property
  have hg : heightReflection hv' ∘ s'.leaf = s.leaf := by
    rw [hleaf]
    funext q
    simp only [comp_apply]
    have hvv : (s'.reduction.v : E3) = (s.reduction.v : E3) := congrArg Subtype.val hv
    simp only [hvv, heightReflection_heightReflection]
  have hvalues :
      (fun q => inner Real (s'.reduction.v : E3)
        (s'.reduction.D (s.reduction.reflectedOriginal q))) =
      (fun q => inner Real (s.reduction.v : E3)
        (heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property)
          (s.reduction.D (f q)))) := by
    funext q
    rw [hinit q, hv]
  have hB :
      Neg.neg '' ((fun q => inner Real (s'.reduction.v : E3)
        (s'.reduction.D (s.reduction.reflectedOriginal q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (s'.reduction.v : E3)
            (s'.reduction.D (s.reduction.reflectedOriginal y))) q = 0}) =
      (fun q => inner Real (s.reduction.v : E3) (s.reduction.D (f q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (s.reduction.v : E3) (s.reduction.D (f y))) q = 0} := by
    rw [hvalues, reflected_critical_values]
    simp only [image_image, neg_neg]
  obtain ⟨A, hl, hu, e, he⟩ := ReflectedEnds.exists_back d.ends hv'
    (congrArg Subtype.val hv) hg hB hcore
  exact ⟨A, hl, hu, e, fun i => he i⟩

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Planar

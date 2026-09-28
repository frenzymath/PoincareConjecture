import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusSquares
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMinimum

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "A2" => squareAnnulus 8 1
local notation "I" => Icc (0 : ℝ) 1

theorem finitePiecewiseAffineOn_annulus_depth
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite) (L : ℝ) :
    FinitePiecewiseAffineOn (depth L) K.space := by
  have hx := (K.affineOnFaces_affine
    (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hy := (K.affineOnFaces_affine
    (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hx' := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ P2 L -
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap)).finitePiecewiseAffineOn hK
  have hy' := (K.affineOnFaces_affine
    (ContinuousAffineMap.const ℝ P2 L -
      (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap)).finitePiecewiseAffineOn hK
  exact (hx.min hy).min (hx'.min hy')

noncomputable def annulusCorrectionHeight (upper : Bool) (p : P2) : ℝ :=
  if upper then (3 + depth 8 p) / 8 else (1 - depth 8 p) / 8

theorem annulusCorrectionHeight_bounds (upper : Bool) (p : A2) :
    annulusCorrectionHeight upper p ∈ I ∧
      (if upper then
        annulusCorrectionHeight upper p ∈ Icc (1 / 4 : ℝ) (1 / 2)
      else annulusCorrectionHeight upper p ∈ Icc (0 : ℝ) (1 / 4)) := by
  have hd := mem_squareAnnulus_iff_depth.mp p.property
  cases upper <;> simp only [annulusCorrectionHeight, Bool.false_eq_true, if_false, if_true]
    <;> constructor <;> constructor <;> linarith [hd.1, hd.2]

theorem finitePiecewiseAffineOn_annulusCorrectionHeight (upper : Bool) :
    FinitePiecewiseAffineOn (annulusCorrectionHeight upper) A2 := by
  obtain ⟨K, hK, hKs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (show (0 : ℝ) < 1 by norm_num) (show (4 : ℝ) * 1 < 8 by norm_num)
  have hd := finitePiecewiseAffineOn_annulus_depth K hK 8
  let f : ℝ →ᴬ[ℝ] ℝ := if upper then
    (1 / 8 : ℝ) • (ContinuousAffineMap.const ℝ ℝ 3 + ContinuousAffineMap.id ℝ ℝ)
    else (1 / 8 : ℝ) • (ContinuousAffineMap.const ℝ ℝ 1 - ContinuousAffineMap.id ℝ ℝ)
  have hf : FinitePiecewiseAffineOn (f ∘ depth 8) A2 := hKs ▸ hd.postcomp f
  apply hf.congr
  intro p _
  cases upper <;> simp only [Function.comp_apply, f, annulusCorrectionHeight,
    Bool.false_eq_true, if_false, if_true, ContinuousAffineMap.smul_apply,
    ContinuousAffineMap.add_apply, ContinuousAffineMap.sub_apply,
    ContinuousAffineMap.coe_const, ContinuousAffineMap.coe_id, Function.const_apply,
    id_eq, smul_eq_mul] <;> ring

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in

theorem exists_correction_annulus_graph
    {L : SimplicialComplex ℝ E} {c : E × ℝ → F}
    (hc : FinitePiecewiseAffineOn c (L.space ×ˢ I)) (hi : InjOn c (L.space ×ˢ I))
    {S : Set E} (hSL : S ⊆ L.space) (a : A2 ≃ₜ S) (ha : a.IsFinitePL) (upper : Bool) :
    ∃ (T : Set F) (b : A2 ≃ₜ T), b.IsFinitePL ∧
      ∀ p : A2, (b p : F) = c ((a p : E), annulusCorrectionHeight upper p) := by
  obtain ⟨f, hf, hfv⟩ := ha
  let g : P2 → E × ℝ := fun p ↦ (f p, annulusCorrectionHeight upper p)
  have hg : FinitePiecewiseAffineOn g A2 :=
    hf.prod_mk (finitePiecewiseAffineOn_annulusCorrectionHeight upper)
  have hgmap : MapsTo g A2 (L.space ×ˢ I) := by
    intro p hp
    refine ⟨?_, (annulusCorrectionHeight_bounds upper ⟨p, hp⟩).1⟩
    change f p ∈ L.space
    rw [← hfv ⟨p, hp⟩]
    exact hSL (a ⟨p, hp⟩).property
  have hk : FinitePiecewiseAffineOn (c ∘ g) A2 := hc.comp hg hgmap
  have hki : InjOn (c ∘ g) A2 := by
    intro p hp q hq heq
    have hpair := hi (hgmap hp) (hgmap hq) heq
    have hfirst := congrArg Prod.fst hpair
    have hval : (a ⟨p, hp⟩ : E) = (a ⟨q, hq⟩ : E) :=
      (hfv ⟨p, hp⟩).trans (hfirst.trans (hfv ⟨q, hq⟩).symm)
    exact congrArg Subtype.val (a.injective (Subtype.ext hval))
  obtain ⟨b, hb, hbval⟩ := hk.exists_homeomorph_image hki
  refine ⟨_, b, hb, ?_⟩
  intro p
  rw [hbval]
  change c (f p, annulusCorrectionHeight upper p) = _
  rw [← hfv p]

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in

theorem correction_annulus_graph_eq_iff
    {L : SimplicialComplex ℝ E} {c : E × ℝ → F}
    (hi : InjOn c (L.space ×ˢ I))
    (a b : A2 → E) (ha : ∀ p, a p ∈ L.space) (hb : ∀ p, b p ∈ L.space)
    (p q : A2) :
    c (a p, annulusCorrectionHeight true p) = c (b q, annulusCorrectionHeight false q) ↔
      a p = b q ∧ depth 8 p = -1 ∧ depth 8 q = -1 := by
  have hp := mem_squareAnnulus_iff_depth.mp p.property
  have hq := mem_squareAnnulus_iff_depth.mp q.property
  constructor
  · intro heq
    have hpair := hi ⟨ha p, (annulusCorrectionHeight_bounds true p).1⟩
      ⟨hb q, (annulusCorrectionHeight_bounds false q).1⟩ heq
    have hfirst := congrArg Prod.fst hpair
    have hh := congrArg Prod.snd hpair
    change (3 + depth 8 p) / 8 = (1 - depth 8 q) / 8 at hh
    exact ⟨hfirst, by linarith [hp.1, hq.1], by linarith [hp.1, hq.1]⟩
  · rintro ⟨hab, hpdepth, hqdepth⟩
    simp only [annulusCorrectionHeight, Bool.false_eq_true, if_false, if_true,
      hpdepth, hqdepth, hab]
    norm_num

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] in

theorem correction_annulus_graph_clearance
    {L : SimplicialComplex ℝ E} {c : E × ℝ → F} {D : Set F}
    (hD : ∀ z ∈ L.space ×ˢ I, c z ∈ D ↔ (1 / 2 : ℝ) ≤ z.2)
    (a : A2 → E) (ha : ∀ p, a p ∈ L.space) (p : A2) :
    (c (a p, annulusCorrectionHeight true p) ∈ D ↔ depth 8 p = 1) ∧
      c (a p, annulusCorrectionHeight false p) ∉ D := by
  have hp := mem_squareAnnulus_iff_depth.mp p.property
  have hu := hD (a p, annulusCorrectionHeight true p)
    ⟨ha p, (annulusCorrectionHeight_bounds true p).1⟩
  have hl := hD (a p, annulusCorrectionHeight false p)
    ⟨ha p, (annulusCorrectionHeight_bounds false p).1⟩
  constructor
  · exact hu.trans ⟨fun h ↦ by change 1 / 2 ≤ (3 + depth 8 p) / 8 at h; linarith [hp.2],
      fun h ↦ by change 1 / 2 ≤ (3 + depth 8 p) / 8; linarith⟩
  · intro h
    have hh := hl.mp h
    change 1 / 2 ≤ (1 - depth 8 p) / 8 at hh
    linarith [hp.1]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [NormedSpace ℝ F] in

theorem correction_annulus_graph_frontier
    {L : SimplicialComplex ℝ E} {c : E × ℝ → F} {R : Set F}
    (hfront : ∀ z ∈ L.space ×ˢ I, c z ∈ frontier R ↔ z.2 = 0)
    (a : A2 → E) (ha : ∀ p, a p ∈ L.space) (p : A2) :
    c (a p, annulusCorrectionHeight true p) ∉ frontier R ∧
      (c (a p, annulusCorrectionHeight false p) ∈ frontier R ↔ depth 8 p = 1) := by
  have hp := mem_squareAnnulus_iff_depth.mp p.property
  have hu := hfront (a p, annulusCorrectionHeight true p)
    ⟨ha p, (annulusCorrectionHeight_bounds true p).1⟩
  have hl := hfront (a p, annulusCorrectionHeight false p)
    ⟨ha p, (annulusCorrectionHeight_bounds false p).1⟩
  constructor
  · intro h
    have hh := hu.mp h
    change (3 + depth 8 p) / 8 = 0 at hh
    linarith [hp.1]
  · exact hl.trans ⟨fun h ↦ by change (1 - depth 8 p) / 8 = 0 at h; linarith,
      fun h ↦ by change (1 - depth 8 p) / 8 = 0; linarith⟩

end PoincareConjecture.M76.Dehn

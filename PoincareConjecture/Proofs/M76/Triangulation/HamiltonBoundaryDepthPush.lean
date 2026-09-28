import PoincareConjecture.Proofs.M76.Mathlib.SupportedPlanarShear
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "I" => Icc (0 : ℝ) (1 / 8)

private noncomputable def inwardDepth (h t : ℝ) : ℝ := max t ((t + h) / 2)

private theorem inwardDepth_strictMono (h : ℝ) : StrictMono (inwardDepth h) := by
  intro s t hst
  exact max_lt_max hst (by linarith)

private theorem inwardDepth_bounds {h t : ℝ} (hh : h ∈ I) (ht : t ∈ I) :
    inwardDepth h t ∈ I := by
  exact ⟨ht.1.trans (le_max_left _ _), max_le ht.2 (by linarith [hh.2, ht.2])⟩

private theorem inwardDepth_zero {h t : ℝ} (hh : h ∈ I) (ht : t ∈ I) :
    inwardDepth h t = 0 ↔ t = 0 ∧ h = 0 := by
  constructor
  · intro he
    have ht0 : t ≤ 0 := he ▸ le_max_left t ((t + h) / 2)
    have hh0 : (t + h) / 2 ≤ 0 := he ▸ le_max_right t ((t + h) / 2)
    exact ⟨by linarith [ht.1], by linarith [ht.1, hh.1]⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [inwardDepth]

noncomputable def inwardBoundaryDepthMap {E : Type*} (h : E → ℝ)
    (p : E × ℝ) : E × ℝ := (p.1, inwardDepth (h p.1) p.2)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {S : Set E}

theorem inwardBoundaryDepthMap_properties (h : E → ℝ)
    (hPL : FinitePiecewiseAffineOn h S) (hbound : MapsTo h S I) :
    FinitePiecewiseAffineOn (inwardBoundaryDepthMap h) (S ×ˢ I) ∧
      Function.Injective (inwardBoundaryDepthMap h) ∧
      MapsTo (inwardBoundaryDepthMap h) (S ×ˢ I) (S ×ˢ I) ∧
      (∀ p ∈ S ×ˢ I, (inwardBoundaryDepthMap h p).2 = 0 ↔ p.2 = 0 ∧ h p.1 = 0) ∧
      (∀ p ∈ S ×ˢ I, p.2 = 1 / 8 → inwardBoundaryDepthMap h p = p) ∧
      ∀ p ∈ S ×ˢ I, h p.1 = 0 → inwardBoundaryDepthMap h p = p := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 / 8 by norm_num)
  have hidI : FinitePiecewiseAffineOn (id : ℝ → ℝ) I :=
    hJI ▸ (J.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)).finitePiecewiseAffineOn hJ
  have hprod := hPL.prodMap hidI
  obtain ⟨K, hK, hKS, _⟩ := hprod
  have hfst : FinitePiecewiseAffineOn (Prod.fst : E × ℝ → E) (S ×ˢ I) :=
    hKS ▸ (K.affineOnFaces_affine
      (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have ht : FinitePiecewiseAffineOn (Prod.snd : E × ℝ → ℝ) (S ×ˢ I) :=
    hKS ▸ (K.affineOnFaces_affine
      (ContinuousLinearMap.snd ℝ E ℝ).toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hh : FinitePiecewiseAffineOn (fun p : E × ℝ => h p.1) (S ×ˢ I) :=
    hPL.comp hfst (fun _ hp => hp.1)
  have havg : FinitePiecewiseAffineOn (fun p : E × ℝ => (p.2 + h p.1) / 2) (S ×ˢ I) := by
    convert (ht.add hh).postcomp
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap using 1
    ext p
    change (p.2 + h p.1) / 2 = (1 / 2 : ℝ) * (p.2 + h p.1)
    ring
  refine ⟨hfst.prod_mk (ht.max havg), ?_, ?_, ?_, ?_, ?_⟩
  · intro p q hpq
    change (p.1, inwardDepth (h p.1) p.2) = (q.1, inwardDepth (h q.1) q.2) at hpq
    have hfirst := congrArg (fun v : E × ℝ => v.1) hpq
    change p.1 = q.1 at hfirst
    have hsecond := congrArg (fun v : E × ℝ => v.2) hpq
    change inwardDepth (h p.1) p.2 = inwardDepth (h q.1) q.2 at hsecond
    rw [← hfirst] at hsecond
    exact Prod.ext hfirst ((inwardDepth_strictMono _).injective hsecond)
  · intro p hp
    exact ⟨hp.1, inwardDepth_bounds (hbound hp.1) hp.2⟩
  · intro p hp
    exact inwardDepth_zero (hbound hp.1) hp.2
  · intro p hp he
    apply Prod.ext
    · rfl
    change max p.2 ((p.2 + h p.1) / 2) = p.2
    exact max_eq_left (by linarith [(hbound hp.1).2])
  · intro p hp he
    apply Prod.ext
    · rfl
    change max p.2 ((p.2 + h p.1) / 2) = p.2
    rw [he, add_zero]
    exact max_eq_left (by linarith [hp.2.1])

end PoincareConjecture.M76

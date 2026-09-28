import PoincareConjecture.Proofs.M76.Mathlib.TriangularCornerRimIntervals
import PoincareConjecture.Proofs.M76.Mathlib.MarkedFinitePLBallCharts
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem IsFinitePLBallPair.exists_small_pointed_rim_width_intervals
    {d b : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d b)
    {f : E → ℝ} (hf : FinitePiecewiseAffineOn f b)
    (q : b) (hzero : f q = 0) (hpos : ∀ x ∈ b, x ≠ q → 0 < f x) :
    ∃ η : ℝ, 0 < η ∧ ∀ c ∈ Ioo 0 η,
      IsFinitePLBallPair ℝ (b ∩ {x | f x ≤ c}) (b ∩ {x | f x = c}) ∧
      IsFinitePLBallPair ℝ (b ∩ {x | c ≤ f x}) (b ∩ {x | f x = c}) := by
  have hz : ((0, 0) : ℝ × ℝ) ∈ frontier base := by
    rw [frontier_base]
    norm_num [roof]
  obtain ⟨e, he, heb, heq⟩ :=
    hd.exists_homeomorph_boundary_point isFinitePLBallPair_base q ⟨(0, 0), hz⟩
  have hcopy := hf
  obtain ⟨J, hJ, hJb, _⟩ := hcopy
  let eb := e.restrictSubsets hd.1 isCompact_base.isClosed.frontier_subset heb
  have hebPL : eb.IsFinitePL :=
    he.restrictSubsets hd.1 isCompact_base.isClosed.frontier_subset heb J hJ hJb
  have heq' : eb q = ⟨(0, 0), hz⟩ := by
    apply Subtype.ext
    change (e ⟨q, hd.1 q.property⟩ : ℝ × ℝ) = (0, 0)
    exact congrArg (fun y : base => (y : ℝ × ℝ)) heq
  obtain ⟨g, hg, hgval⟩ := hebPL.symm
  have hgmap : MapsTo g (frontier base) b := fun x hx =>
    hgval ⟨x, hx⟩ ▸ (eb.symm ⟨x, hx⟩).property
  have hginj : InjOn g (frontier base) := by
    intro x hx y hy hxy
    have h : eb.symm ⟨x, hx⟩ = eb.symm ⟨y, hy⟩ := by
      apply Subtype.ext
      simpa only [hgval] using hxy
    exact congrArg Subtype.val (eb.symm.injective h)
  have hgzero : g (0, 0) = q := by
    rw [← hgval ⟨(0, 0), hz⟩, ← heq', eb.symm_apply_apply]
  have hfg : FinitePiecewiseAffineOn (f ∘ g) (frontier base) := hf.comp hg hgmap
  have hfgzero : (f ∘ g) (0, 0) = 0 := by
    change f (g (0, 0)) = 0
    rw [hgzero, hzero]
  have hfgpos (p : ℝ × ℝ) (hp : p ∈ frontier base) (hp0 : p ≠ (0, 0)) :
      0 < (f ∘ g) p :=
    hpos _ (hgmap hp) (fun h => hp0 (hginj hp hz (h.trans hgzero.symm)))
  obtain ⟨η, hη, hlevels⟩ := exists_small_corner_rim_intervals hfg hfgzero hfgpos
  have hforward := hebPL
  obtain ⟨k, _, hkval⟩ := hforward
  have hkmap (x : E) (hx : x ∈ b) : k x ∈ frontier base :=
    hkval ⟨x, hx⟩ ▸ (eb ⟨x, hx⟩).property
  have hgk (x : E) (hx : x ∈ b) : g (k x) = x := by
    rw [← hkval ⟨x, hx⟩, ← hgval (eb ⟨x, hx⟩), eb.symm_apply_apply]
  have hpre (P : ℝ → Prop) :
      b ∩ k ⁻¹' (frontier base ∩ {p | P ((f ∘ g) p)}) = b ∩ {x | P (f x)} := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      have h : P (f (g (k x))) := hx.2.2
      rwa [hgk x hx.1] at h
    · intro hx
      refine ⟨hx.1, hkmap x hx.1, ?_⟩
      change P (f (g (k x)))
      rw [hgk x hx.1]
      exact hx.2
  refine ⟨η, hη, fun c hc => ?_⟩
  obtain ⟨hlo, hhi⟩ := hlevels c hc
  have hlo' := hebPL.preimage_ballPair hlo inter_subset_left hkval
  have hhi' := hebPL.preimage_ballPair hhi inter_subset_left hkval
  rw [hpre (fun r => r ≤ c), hpre (fun r => r = c)] at hlo'
  rw [hpre (fun r => c ≤ r), hpre (fun r => r = c)] at hhi'
  exact ⟨hlo', hhi'⟩

end Set

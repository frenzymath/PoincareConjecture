import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem FinitePiecewiseAffineOn.prodMap {f : E → G} {g : F → H} {s : Set E} {t : Set F}
    (hf : FinitePiecewiseAffineOn f s) (hg : FinitePiecewiseAffineOn g t) :
    FinitePiecewiseAffineOn (Prod.map f g) (s ×ˢ t) := by
  obtain ⟨K, hK, rfl, hfa⟩ := hf
  obtain ⟨J, hJ, rfl, hga⟩ := hg
  obtain ⟨L, hL, hspace, hcells⟩ := K.exists_finite_triangulation_prod J hK hJ
  refine ⟨L, hL, hspace, ?_⟩
  intro q hq
  obtain ⟨s, hs, t, ht, hqt⟩ := hcells q hq
  obtain ⟨a, ha⟩ := hfa s hs
  obtain ⟨b, hb⟩ := hga t ht
  refine ⟨a.prodMap b, fun x hx => ?_⟩
  exact Prod.ext (ha (hqt hx).1) (hb (hqt hx).2)

end Geometry

namespace Homeomorph

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem IsFinitePL.prod {s : Set E} {t : Set F} {u : Set G} {v : Set H}
    {e : s ≃ₜ u} {d : t ≃ₜ v} (he : e.IsFinitePL) (hd : d.IsFinitePL) :
    ((Homeomorph.Set.prod s t).trans
      ((e.prodCongr d).trans (Homeomorph.Set.prod u v).symm)).IsFinitePL := by
  obtain ⟨f, hf, heval⟩ := he
  obtain ⟨g, hg, hdval⟩ := hd
  refine ⟨Prod.map f g, hf.prodMap hg, fun p => ?_⟩
  exact Prod.ext (heval ⟨(p : E × F).1, p.property.1⟩)
    (hdval ⟨(p : E × F).2, p.property.2⟩)

end Homeomorph

namespace Set

variable {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in

theorem IsFinitePLBallPair.prod {s b : Set X} {t c : Set Y}
    (hs : IsFinitePLBallPair E s b) (ht : IsFinitePLBallPair F t c) :
    IsFinitePLBallPair (E × F) (s ×ˢ t) ((b ×ˢ t) ∪ (s ×ˢ c)) := by
  obtain ⟨hbs, C, hC, hCcv, hCne, e, he, heb⟩ := hs
  obtain ⟨hct, D, hD, hDcv, hDne, d, hd, hdc⟩ := ht
  let H := (Homeomorph.Set.prod s t).trans
    ((e.prodCongr d).trans (Homeomorph.Set.prod C D).symm)
  have hne : (interior (C ×ˢ D)).Nonempty := by
    rw [interior_prod_eq]
    exact hCne.prod hDne
  refine ⟨union_subset (prod_mono hbs Subset.rfl) (prod_mono Subset.rfl hct),
    C ×ˢ D, hC.prod hD, hCcv.prod hDcv, hne, H, he.prod hd, ?_⟩
  intro p
  let x : s := ⟨(p : X × Y).1, p.property.1⟩
  let y : t := ⟨(p : X × Y).2, p.property.2⟩
  change (((p : X × Y).1 ∈ b ∧ (p : X × Y).2 ∈ t) ∨
    ((p : X × Y).1 ∈ s ∧ (p : X × Y).2 ∈ c)) ↔
      ((e x : E), (d y : F)) ∈ frontier (C ×ˢ D)
  rw [frontier_prod_eq, hC.isClosed.closure_eq, hD.isClosed.closure_eq]
  change (((x : X) ∈ b ∧ (y : Y) ∈ t) ∨ ((x : X) ∈ s ∧ (y : Y) ∈ c)) ↔
    (((e x : E) ∈ C ∧ (d y : F) ∈ frontier D) ∨
      ((e x : E) ∈ frontier C ∧ (d y : F) ∈ D))
  simp only [x.property, y.property, (e x).property, (d y).property,
    true_and, and_true, ← heb x, ← hdc y]
  exact or_comm

end Set

import PoincareConjecture.Proofs.M76.PrimeReduction.BoundaryTriangleProducts

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K L : SimplicialComplex ℝ E) [Fintype K.faces]

local notation "I" => Icc (0 : ℝ) 1

structure BoundaryTriangleFibers where
  map : Finset E → ℝ → E
  piecewiseAffine : ∀ s ∈ L.faces, s.card = 3 → FinitePiecewiseAffineOn (map s) I
  injective : ∀ s ∈ L.faces, s.card = 3 → InjOn (map s) I
  image_eq : ∀ s ∈ L.faces, s.card = 3 → map s '' I = (K.barycentricDualBlock s).space
  central : ∀ s ∈ L.faces, s.card = 3 → map s 0 = s.centroid ℝ id
  boundary : ∀ s ∈ L.faces, s.card = 3 → ∀ r ∈ I, map s r ∈ L.space ↔ r = 0
  formula : ∀ s ∈ L.faces, s.card = 3 → ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4 ∧
    ∀ r ∈ I, map s r = AffineMap.lineMap (s.centroid ℝ id) (t.centroid ℝ id) r

theorem exists_boundary_triangle_fibers [Finite L.faces] (hLK : L ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 4)
    (hboundary : ∀ s ∈ L.faces, ∃ t ∈ L.faces, s ⊆ t ∧ t.card = 3)
    (hfacets : ∀ s ∈ L.faces, s.card = 3 →
      {t | t ∈ K.faces ∧ t.card = 4 ∧ s ⊆ t}.ncard = 1) :
    Nonempty (BoundaryTriangleFibers K L) := by
  classical
  let S := {s : Finset E // s ∈ L.faces ∧ s.card = 3}
  have hex (s : S) : ∃ f : ℝ → E, FinitePiecewiseAffineOn f I ∧ InjOn f I ∧
      f '' I = (K.barycentricDualBlock s).space ∧ f 0 = s.val.centroid ℝ id ∧
      (∀ r ∈ I, f r ∈ L.space ↔ r = 0) ∧
      ∃ t ∈ K.faces, s.val ⊆ t ∧ t.card = 4 ∧ ∀ r ∈ I,
        f r = AffineMap.lineMap (s.val.centroid ℝ id) (t.centroid ℝ id) r := by
    obtain ⟨t, ht, hst, htc, J, hJ, hval, hproper⟩ :=
      K.exists_boundary_triangle_products L hLK hpure hboundary hfacets
        s.property.1 s.property.2
    obtain ⟨f, hf, hJf⟩ := hJ
    have hformula (r : ℝ) (hr : r ∈ I) :
        f r = AffineMap.lineMap (s.val.centroid ℝ id) (t.centroid ℝ id) r :=
      (hJf ⟨r, hr⟩).symm.trans (hval ⟨r, hr⟩)
    refine ⟨f, hf, ?_, ?_, ?_, ?_, t, ht, hst, htc, hformula⟩
    · intro r hr q hq he
      have he' : J ⟨r, hr⟩ = J ⟨q, hq⟩ := by
        apply Subtype.ext
        exact (hJf ⟨r, hr⟩).trans (he.trans (hJf ⟨q, hq⟩).symm)
      exact congrArg Subtype.val (J.injective he')
    · ext y
      constructor
      · rintro ⟨r, hr, rfl⟩
        rw [← hJf ⟨r, hr⟩]
        exact (J ⟨r, hr⟩).property
      · intro hy
        refine ⟨J.symm ⟨y, hy⟩, (J.symm ⟨y, hy⟩).property, ?_⟩
        rw [← hJf, J.apply_symm_apply]
    · simpa only [AffineMap.lineMap_apply_zero] using hformula 0 ⟨le_rfl, zero_le_one⟩
    · intro r hr
      rw [← hJf ⟨r, hr⟩]
      exact hproper ⟨r, hr⟩
  choose F hF hi him h0 hb hformula using hex
  let f : Finset E → ℝ → E := fun s =>
    if h : s ∈ L.faces ∧ s.card = 3 then F ⟨s, h⟩ else fun _ => 0
  have hval (s : S) : f s = F s := by
    simp only [f, dif_pos s.property]
    rfl
  refine ⟨⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hF ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hi ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact him ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact h0 ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hb ⟨s, hs, hc⟩
  · intro s hs hc
    rw [hval ⟨s, hs, hc⟩]
    exact hformula ⟨s, hs, hc⟩

end Geometry.SimplicialComplex

import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Horoball

set_option autoImplicit false

open Set Metric

namespace Poincare.Riemannian.Soul

variable {M : Type*} [MetricSpace M]

private def exhaustionValues (p x : M) : Set ℝ :=
  {0} ∪ range (fun ray : {ray : ℝ → M // IsRay ray ∧ ray 0 = p} => -busemann ray.val x)

noncomputable def busemannExhaustion (p x : M) : ℝ := sSup (exhaustionValues p x)

private theorem exhaustionValues_nonempty (p x : M) : (exhaustionValues p x).Nonempty :=
  ⟨0, Or.inl rfl⟩

private theorem exhaustionValues_bddAbove (p x : M) : BddAbove (exhaustionValues p x) := by
  refine ⟨dist x p, ?_⟩
  rintro r (hr | ⟨ray, rfl⟩)
  · simpa only [mem_singleton_iff.mp hr] using (dist_nonneg : 0 ≤ dist x p)
  · have h := neg_dist_le_busemann ray.property.1 x
    rw [ray.property.2] at h
    linarith

theorem busemannExhaustion_nonneg (p x : M) : 0 ≤ busemannExhaustion p x :=
  le_csSup (exhaustionValues_bddAbove p x) (Or.inl rfl)

theorem neg_busemann_le_exhaustion {p : M} {ray : ℝ → M}
    (hray : IsRay ray) (hray0 : ray 0 = p) (x : M) :
    -busemann ray x ≤ busemannExhaustion p x :=
  le_csSup (exhaustionValues_bddAbove p x) (Or.inr ⟨⟨ray, hray, hray0⟩, rfl⟩)

theorem busemannExhaustion_le_iff {p x : M} {r : ℝ} (hr : 0 ≤ r) :
    busemannExhaustion p x ≤ r ↔ x ∈ horoballIntersection p r := by
  constructor
  · intro h ray hray hray0
    have := (neg_busemann_le_exhaustion hray hray0 x).trans h
    linarith
  · intro h
    apply csSup_le (exhaustionValues_nonempty p x)
    rintro v (hv | ⟨ray, rfl⟩)
    · simpa only [mem_singleton_iff.mp hv] using hr
    · have := h ray.val ray.property.1 ray.property.2
      linarith

theorem busemannExhaustion_le_dist (p x : M) : busemannExhaustion p x ≤ dist x p :=
  (busemannExhaustion_le_iff dist_nonneg).mpr
    (closedBall_subset_horoballIntersection p (dist x p) (by simp))

@[simp] theorem busemannExhaustion_self (p : M) : busemannExhaustion p p = 0 :=
  le_antisymm (by simpa only [dist_self] using busemannExhaustion_le_dist p p)
    (busemannExhaustion_nonneg p p)

theorem lipschitz_busemannExhaustion (p : M) : LipschitzWith 1 (busemannExhaustion p) := by
  apply LipschitzWith.of_le_add
  intro x y
  apply csSup_le (exhaustionValues_nonempty p x)
  rintro v (hv | ⟨ray, rfl⟩)
  · rw [mem_singleton_iff.mp hv]
    exact add_nonneg (busemannExhaustion_nonneg p y) dist_nonneg
  · have h := (lipschitz_busemann ray.property.1).le_add_mul y x
    have hb := neg_busemann_le_exhaustion ray.property.1 ray.property.2 y
    simp only [NNReal.coe_one, one_mul, dist_comm y x] at h
    linarith

theorem convexOn_busemannExhaustion_comp {p : M} {curve : ℝ → M} {a b : ℝ}
    (hconc : ∀ ray : ℝ → M, IsRay ray → ray 0 = p →
      ConcaveOn ℝ (Icc a b) (busemann ray ∘ curve)) :
    ConvexOn ℝ (Icc a b) (busemannExhaustion p ∘ curve) := by
  refine ⟨convex_Icc a b, ?_⟩
  intro u hu v hv α β hα hβ hsum
  simp only [Function.comp_apply, smul_eq_mul]
  apply csSup_le (exhaustionValues_nonempty p (curve (α * u + β * v)))
  rintro r (hr | ⟨ray, rfl⟩)
  · rw [mem_singleton_iff.mp hr]
    exact add_nonneg (mul_nonneg hα (busemannExhaustion_nonneg p _))
      (mul_nonneg hβ (busemannExhaustion_nonneg p _))
  · have h := (hconc ray.val ray.property.1 ray.property.2).2 hu hv hα hβ hsum
    have huB := neg_busemann_le_exhaustion ray.property.1 ray.property.2 (curve u)
    have hvB := neg_busemann_le_exhaustion ray.property.1 ray.property.2 (curve v)
    simp only [Function.comp_apply, smul_eq_mul] at h
    nlinarith [mul_le_mul_of_nonneg_left huB hα, mul_le_mul_of_nonneg_left hvB hβ]

end Poincare.Riemannian.Soul

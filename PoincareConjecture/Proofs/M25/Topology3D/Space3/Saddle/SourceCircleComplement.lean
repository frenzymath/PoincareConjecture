import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CircleIntervalComplement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.CircleAngularGeometry

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_source_circle_complement
    (q : UnitCircle → UnitTwoSphere) (hq : Continuous q) (hqi : Injective q)
    (gamma : unitInterval → UnitTwoSphere) (hg : Continuous gamma) (hgi : Injective gamma)
    (hsub : range gamma ⊆ range q) :
    ∃ a v eta : ℝ,
    let P : ℝ → UnitTwoSphere := fun t =>
      q (complexUnitCircleHomeomorph (Circle.exp (a + v * t)))
    0 < |v| ∧ |v| < 2 * Real.pi ∧ 0 < eta ∧ eta < 1 / 8 ∧
      Continuous P ∧ InjOn P (Icc (-eta) (1 + eta)) ∧
      P 0 = gamma 0 ∧ P 1 = gamma 1 ∧
      range q \ range gamma = P '' Ioo (0 : ℝ) 1 ∧
      range q \ (gamma '' Ioo (0 : unitInterval) 1) = P '' Icc (0 : ℝ) 1 ∧
      (∀ t ∈ Ioo (-eta) (0 : ℝ), P t ∈ gamma '' Ioo (0 : unitInterval) 1) ∧
      ∀ t ∈ Ioo (1 : ℝ) (1 + eta), P t ∈ gamma '' Ioo (0 : unitInterval) 1 := by
  classical
  let Q : Circle → UnitTwoSphere := q ∘ complexUnitCircleHomeomorph
  have hQ : Continuous Q := hq.comp complexUnitCircleHomeomorph.continuous
  have hQi : Injective Q := hqi.comp complexUnitCircleHomeomorph.injective
  have hQr : range Q = range q := by
    change range (q ∘ complexUnitCircleHomeomorph) = range q
    rw [range_comp, complexUnitCircleHomeomorph.surjective.range_eq, image_univ]
  have hsubQ : range gamma ⊆ range Q := hQr.symm ▸ hsub
  let e : Circle ≃ₜ range Q := (hQ.isClosedEmbedding hQi).isEmbedding.toHomeomorph
  let f : unitInterval → Circle := fun t => e.symm ⟨gamma t, hsubQ ⟨t, rfl⟩⟩
  have hf : Continuous f := e.symm.continuous.comp (hg.subtype_mk _)
  have hrec (t : unitInterval) : Q (f t) = gamma t :=
    congrArg Subtype.val (e.apply_symm_apply ⟨gamma t, hsubQ ⟨t, rfl⟩⟩)
  have hfi : Injective f := by
    intro t s hts
    apply hgi
    rw [← hrec t, ← hrec s, hts]
  have hrecFun : Q ∘ f = gamma := funext hrec
  have hgr : Q '' range f = range gamma := by
    rw [← range_comp, hrecFun]
  have hgo : Q '' (f '' Ioo (0 : unitInterval) 1) = gamma '' Ioo (0 : unitInterval) 1 := by
    rw [← image_comp, hrecFun]
  have hdiff (T : Set Circle) : range Q \ (Q '' T) = Q '' Tᶜ := by
    ext y
    constructor
    · rintro ⟨⟨z, rfl⟩, hz⟩
      exact ⟨z, fun ht => hz ⟨z, ht, rfl⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, rfl⟩, ?_⟩
      rintro ⟨w, hw, hwz⟩
      exact hz ((hQi hwz) ▸ hw)
  obtain ⟨a, d, hd, hdpi, hvabs, hv, _, _, _, h0, h1, _, _, ho, hc⟩ :=
    exists_circle_interval_complement f hf hfi
  let v : ℝ := d - if 0 < d then 2 * Real.pi else -(2 * Real.pi)
  let b : ℝ → UnitCircle := fun t => complexUnitCircleHomeomorph (Circle.exp (a + v * t))
  let P : ℝ → UnitTwoSphere := q ∘ b
  have hvpi : |v| < 2 * Real.pi := by
    change |v| = 2 * Real.pi - |d| at hvabs
    rw [hvabs]
    linarith
  obtain ⟨eta, heta, hetalt, hbi, hb0, hb1⟩ := exists_circleAffine_extension a v hv hvpi
  have hP : Continuous P := hq.comp (complexUnitCircleHomeomorph.continuous.comp
    (Circle.exp.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))))
  have hPi : InjOn P (Icc (-eta) (1 + eta)) := by
    intro t ht s hs hts
    exact hbi ht hs (hqi hts)
  have hPo : range q \ range gamma = P '' Ioo (0 : ℝ) 1 := by
    calc
      _ = range Q \ (Q '' range f) := by rw [hQr, hgr]
      _ = Q '' (range f)ᶜ := hdiff _
      _ = Q '' ((fun t : ℝ => Circle.exp (a + v * t)) '' Ioo (0 : ℝ) 1) := by rw [ho]
      _ = P '' Ioo (0 : ℝ) 1 := by rw [image_image]; rfl
  have hPc : range q \ (gamma '' Ioo (0 : unitInterval) 1) = P '' Icc (0 : ℝ) 1 := by
    calc
      _ = range Q \ (Q '' (f '' Ioo (0 : unitInterval) 1)) := by rw [hQr, hgo]
      _ = Q '' (f '' Ioo (0 : unitInterval) 1)ᶜ := hdiff _
      _ = Q '' ((fun t : ℝ => Circle.exp (a + v * t)) '' Icc (0 : ℝ) 1) := by rw [hc]
      _ = P '' Icc (0 : ℝ) 1 := by rw [image_image]; rfl
  refine ⟨a, v, eta, hv, hvpi, heta, hetalt, hP, hPi,
    (congrArg Q h0).trans (hrec 0), (congrArg Q h1).trans (hrec 1), hPo, hPc, ?_, ?_⟩
  · intro t ht
    by_contra hn
    have hm : P t ∈ P '' Icc (0 : ℝ) 1 := by
      rw [← hPc]
      exact ⟨⟨b t, rfl⟩, hn⟩
    obtain ⟨s, hs, hst⟩ := hm
    exact hb0 t ht ⟨s, hs, hqi hst⟩
  · intro t ht
    by_contra hn
    have hm : P t ∈ P '' Icc (0 : ℝ) 1 := by
      rw [← hPc]
      exact ⟨⟨b t, rfl⟩, hn⟩
    obtain ⟨s, hs, hst⟩ := hm
    exact hb1 t ht ⟨s, hs, hqi hst⟩

end PoincareConjecture.M25.Topology3D

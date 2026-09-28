import PoincareConjecture.Proofs.M76.Wall.EndpointArcPairChart
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLPathOperations

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_final_endpoint_arc_pair_chart
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X}
    (hL : PLDomain e L) {f : ℝ → X}
    (hf : PolyhedralPLInCharts e f (Icc (0 : ℝ) 1))
    (hi : InjOn f (Icc (0 : ℝ) 1)) (hfront : f 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ L)
    {W : Set X} (hW : IsOpen W) (hxW : f 1 ∈ W) :
    ∃ (G : OpenPartialHomeomorph X V3) (A : V3 →L[ℝ] ℝ) (v : V3),
      f 1 ∈ G.source ∧ G.source ⊆ W ∧ G (f 1) = 0 ∧ A v = 1 ∧
      (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧
      (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ A (G y)) ∧
      (∀ y ∈ G.source, y ∈ frontier L ↔ A (G y) = 0) ∧
      ∀ y ∈ G.source,
        y ∈ f '' Icc (0 : ℝ) 1 ↔ ∃ r : ℝ, r ≤ 0 ∧ G y = r • v := by
  let p : Path (f 0) (f 1) := Path.ofLine hf.continuousOn rfl rfl
  have hp : PolyhedralPLInCharts e p.extend (Icc (0 : ℝ) 1) :=
    hf.congr (fun _ ht => (p.extend_apply ht).symm)
  have hreflect {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : 1 - t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hvalue (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : p.symm.extend t = f (1 - t) := by
    rw [p.extend_symm_apply, p.extend_apply (hreflect ht)]
    rfl
  have hpi : InjOn p.symm.extend (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    rw [hvalue s hs, hvalue t ht] at hst
    have heq := hi (hreflect hs) (hreflect ht) hst
    linarith
  have hp0 : p.symm.extend 0 = f 1 := p.symm.extend_zero
  have hproperp (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : p.symm.extend t ∉ L := by
    rw [hvalue t ⟨ht.1.le, ht.2.le⟩]
    exact hproper (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have himage : p.symm.extend '' Icc (0 : ℝ) 1 = f '' Icc (0 : ℝ) 1 := by
    rw [p.symm.image_extend_of_subset subset_rfl, Path.symm_range]
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  obtain ⟨G, A, v, hxG, hGW, hzero, hv, hcompat, hhalf, hboundary, harc⟩ :=
    hL.exists_endpoint_arc_pair_chart (p.polyhedralPL_extend_symm hp) hpi
      (by simpa only [hp0] using hfront) hproperp hW (by simpa only [hp0] using hxW)
  refine ⟨G, A, v, ?_, hGW, ?_, hv, hcompat, hhalf, hboundary, ?_⟩
  · simpa only [hp0] using hxG
  · simpa only [hp0] using hzero
  · intro y hy
    simpa only [himage] using harc y hy

end PoincareConjecture.M76

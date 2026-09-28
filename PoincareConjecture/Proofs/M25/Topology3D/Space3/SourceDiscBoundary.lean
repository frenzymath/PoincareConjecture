import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceSphereSplit













set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

attribute [local instance] space3_stereographic_dimension



theorem source_sphere_two_parametrized_discs_of_planar (hP : PlanarSchoenfliesService)
    (q : UnitCircle → UnitTwoSphere) (hq : ContMDiff (𝓡 1) (𝓡 2) ∞ q)
    (hqi : Injective q) (hqd : ∀ θ, Injective (mfderiv (𝓡 1) (𝓡 2) q θ))
    (v : UnitTwoSphere) (hv : v ∉ range q) :
    ∃ e f : OpenPartialHomeomorph E2 UnitTwoSphere,
      closedBall 0 1 ⊆ e.source ∧ closedBall 0 1 ⊆ f.source ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ e.symm e.target ∧
      ContMDiffOn 𝓘(ℝ, E2) (𝓡 2) ∞ f f.source ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, E2) ∞ f.symm f.target ∧
      (∀ θ : UnitCircle, e θ.1 = q θ) ∧ (∀ θ : UnitCircle, f θ.1 = q θ) ∧
      (e '' closedBall 0 1) ∪ (f '' closedBall 0 1) = univ ∧
      (e '' closedBall 0 1) ∩ (f '' closedBall 0 1) = range q ∧
      Disjoint (e '' ball 0 1) (f '' ball 0 1) ∧
      (e '' ball 0 1) ∪ (f '' ball 0 1) = (range q)ᶜ := by
  obtain ⟨e, f, hes, hfs, hem, hei, _, _, heq, heb, hfb, hu, hi, hd, ho⟩ :=
    source_sphere_two_discs_of_planar hP q hq hqi hqd v hv
  let w := e 0
  have hwA : w ∈ e '' closedBall 0 1 := ⟨0, mem_closedBall_self zero_le_one, rfl⟩
  have hwq : w ∉ range q := by
    rw [← heb]
    rintro ⟨x, hx, hxw⟩
    have hx0 := e.injOn (hes (sphere_subset_closedBall hx))
      (hes (mem_closedBall_self zero_le_one)) hxw
    have hn := mem_sphere_zero_iff_norm.mp hx
    rw [hx0, norm_zero] at hn
    exact zero_ne_one hn
  have hwf : w ∉ f '' closedBall 0 1 := by
    intro hw
    apply hwq
    rw [← hi]
    exact ⟨hwA, hw⟩
  obtain ⟨D, g, hg, hgs, hgm, hgi, hgq⟩ :=
    exists_source_circle_disc_chart hP q hq hqi hqd w hwq
  have hgb : g '' sphere 0 1 = range q := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hgq ⟨x, hx⟩).symm⟩
    · rintro ⟨θ, rfl⟩
      exact ⟨θ.1, θ.2, hgq θ⟩
  have hwg : w ∉ g '' closedBall 0 1 := by
    rintro ⟨x, _, hxw⟩
    rw [hg] at hxw
    change (stereographic' 2 w).symm (D.chart x) = w at hxw
    have hxsrc := (stereographic' 2 w).map_target
      (show D.chart x ∈ (stereographic' 2 w).target by rw [stereographic'_target]; trivial)
    rw [hxw, stereographic'_source] at hxsrc
    exact hxsrc rfl
  have hdim : 1 < Module.rank ℝ E2 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
  have hdim3 : 1 < Module.rank ℝ E3 :=
    Module.one_lt_rank_of_one_lt_finrank (by simp [E3])
  let : PreconnectedSpace UnitTwoSphere :=
    Subtype.preconnectedSpace (isConnected_sphere hdim3 0 zero_le_one).isPreconnected
  have hclosed : g '' closedBall 0 1 = f '' closedBall 0 1 :=
    compactChart_region_eq_of_boundary_eq g f hdim hgs hfs (hgb.trans hfb.symm) hwg hwf
  have hopen : g '' ball 0 1 = f '' ball 0 1 := by
    rw [← compactChart_interior_closedBall g 0 zero_lt_one hgs,
      ← compactChart_interior_closedBall f 0 zero_lt_one hfs, hclosed]
  refine ⟨e, g, hes, hgs, hem, hei, hgm, hgi, heq, hgq, ?_, ?_, ?_, ?_⟩
  · rwa [hclosed]
  · rwa [hclosed]
  · rwa [hopen]
  · rwa [hopen]

end PoincareConjecture.M25.Topology3D

import PoincareConjecture.Proofs.M38.SmoothSphereLift
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ E]



theorem isImmersion_sphere_lift_through_localDiffeomorph
    (q : E → M) (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    {f : UnitTwoSphere → M} (hf : Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞ f)
    {F : UnitTwoSphere → E} (hF : Continuous F)
    (hlift : ∀ z, q (F z) = f z) :
    Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞ F := by
  apply Manifold.IsImmersionOfComplement.isImmersion (F := hf.complement)
  intro x
  let h := hf.isImmersionOfComplement_complement x
  obtain ⟨φ, hx, heq⟩ := hq (F x)
  let s := F ⁻¹' φ.source
  have hs : IsOpen s := φ.open_source.preimage hF
  let d := h.domChart.restr s
  let b := φ.toOpenPartialHomeomorph.trans h.codChart
  have hds : d.source = h.domChart.source ∩ s := h.domChart.restr_source' s hs
  have hb : b ∈ IsManifold.maximalAtlas (𝓡 3) ∞ E := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        (φ.contMDiffOn.mono inter_subset_left) inter_subset_right
    · exact φ.symm.contMDiffOn.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          inter_subset_left) inter_subset_right
  have hsource (y : UnitTwoSphere) (hy : y ∈ d.source) : F y ∈ b.source := by
    rw [hds] at hy
    change F y ∈ φ.source ∧ φ (F y) ∈ h.codChart.source
    refine ⟨hy.2, ?_⟩
    rw [← heq hy.2, hlift]
    exact h.source_subset_preimage_source hy.1
  have hdx : x ∈ d.source := by
    rw [hds]
    exact ⟨h.mem_domChart_source, hx⟩
  apply Manifold.IsImmersionAtOfComplement.mk_of_charts h.equiv d b hdx
    (hsource x hdx) (restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas hs) hb hsource
  intro v hv
  have hv' : v ∈ d.target := by simpa using hv
  have hdv := d.map_target hv'
  rw [hds] at hdv
  change h.codChart (φ (F (d.symm v))) = h.equiv (v, 0)
  rw [← heq hdv.2, hlift]
  apply h.writtenInCharts
  simpa using hv'.1



theorem exists_smooth_sphere_lift_through_cover [T2Space E]
    (q : E → M) (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hcover : IsCoveringMap q)
    (f : UnitTwoSphere → M) (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (z₀ : UnitTwoSphere) (p₀ : E) (hp₀ : q p₀ = f z₀) :
    ∃ F : UnitTwoSphere → E,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F ∧
      F z₀ = p₀ ∧ ∀ z, q (F z) = f z := by
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  obtain ⟨F, ⟨hF₀, hFq⟩, _⟩ := hcover.existsUnique_continuousMap_lifts
    ⟨f, hf.contMDiff.continuous⟩ z₀ p₀ hp₀
  have hlift (z : UnitTwoSphere) : q (F z) = f z := congrFun hFq z
  have hi := isImmersion_sphere_lift_through_localDiffeomorph q hq
    hf.isImmersion F.continuous hlift
  have hinj : Function.Injective F := by
    intro x y hxy
    exact hf.isEmbedding.injective
      ((hlift x).symm.trans ((congrArg q hxy).trans (hlift y)))
  exact ⟨F, ⟨hi, (F.continuous.isClosedEmbedding hinj).isEmbedding⟩, hF₀, hlift⟩



theorem exists_equivariant_sphere_lifts_through_cover [T2Space E]
    {G : Type*} [Group G] [MulAction G E]
    (q : E → M) (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hcover : IsCoveringMap q) (hsurj : Function.Surjective q)
    (e : G → Diffeomorph (𝓡 3) (𝓡 3) E E ∞)
    (he : ∀ (g : G) (x : E), e g x = g • x)
    (hdeck : ∀ (g : G) (x : E), q (g • x) = q x)
    (hfree : ∀ (g : G) (x : E), g • x = x → g = 1)
    (hfibers : ∀ (x y : E), q x = q y → ∃ g : G, y = g • x)
    (f : UnitTwoSphere → M) (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f) :
    ∃ F : G → UnitTwoSphere → E,
      (∀ g, Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (F g)) ∧
      (∀ g z, q (F g z) = f z) ∧
      (∀ g h z, F (g * h) z = g • F h z) ∧
      (∀ g h, g ≠ h → Disjoint (range (F g)) (range (F h))) ∧
      q ⁻¹' range f = ⋃ g, range (F g) := by
  let z₀ : UnitTwoSphere := Poincare.Topology.standardSpherePole 0
  obtain ⟨p₀, hp₀⟩ := hsurj (f z₀)
  obtain ⟨L, hL, _, hqL⟩ :=
    exists_smooth_sphere_lift_through_cover q hq hcover f hf z₀ p₀ hp₀
  let F : G → UnitTwoSphere → E := fun g z => e g (L z)
  have hF (g : G) : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (F g) :=
    hL.comp_localDiffeomorph (e g).isLocalDiffeomorph
      ((e g).injective.comp hL.isEmbedding.injective)
  have hqF (g : G) (z : UnitTwoSphere) : q (F g z) = f z := by
    change q (e g (L z)) = f z
    rw [he, hdeck, hqL]
  refine ⟨F, hF, hqF, ?_, ?_, ?_⟩
  · intro g h z
    change e (g * h) (L z) = g • e h (L z)
    rw [he, he, mul_smul]
  · intro g h hgh
    apply disjoint_left.mpr
    rintro x ⟨a, ha⟩ ⟨b, hb⟩
    have hab : a = b := hf.isEmbedding.injective
      ((hqF g a).symm.trans ((congrArg q (ha.trans hb.symm)).trans (hqF h b)))
    subst b
    have heq : g • L a = h • L a := by
      simpa only [F, he] using ha.trans hb.symm
    have hfix : (h⁻¹ * g) • L a = L a := by
      rw [mul_smul, heq, inv_smul_smul]
    have hunit := hfree (h⁻¹ * g) (L a) hfix
    exact hgh (by simpa using congrArg (h * ·) hunit)
  · ext x
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨g, hg⟩ := hfibers (L z) x ((hqL z).trans hz)
      exact mem_iUnion.mpr ⟨g, z, by simpa only [F, he] using hg.symm⟩
    · intro hx
      obtain ⟨g, z, rfl⟩ := mem_iUnion.mp hx
      exact ⟨z, (hqF g z).symm⟩

end PoincareConjecture.M38

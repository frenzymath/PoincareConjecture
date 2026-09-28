import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import PoincareConjecture.Definitions.Ch09.NeckCapTopology














set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]



theorem isImmersion_sphere_lift
    (q : UnitThreeSphere → M) (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    {f : UnitTwoSphere → M} (hf : Manifold.IsImmersion (𝓡 2) (𝓡 3) ∞ f)
    {F : UnitTwoSphere → UnitThreeSphere} (hF : Continuous F)
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
  have hdsource : d.source = h.domChart.source ∩ s := h.domChart.restr_source' s hs
  have hb : b ∈ IsManifold.maximalAtlas (𝓡 3) ∞ UnitThreeSphere := by
    apply b.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        (φ.contMDiffOn.mono inter_subset_left) inter_subset_right
    · exact φ.symm.contMDiffOn.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mono
          inter_subset_left) inter_subset_right
  have hsource (y : UnitTwoSphere) (hy : y ∈ d.source) : F y ∈ b.source := by
    rw [hdsource] at hy
    change F y ∈ φ.source ∧ φ (F y) ∈ h.codChart.source
    refine ⟨hy.2, ?_⟩
    rw [← heq hy.2, hlift]
    exact h.source_subset_preimage_source hy.1
  have hdx : x ∈ d.source := by
    rw [hdsource]
    exact ⟨h.mem_domChart_source, hx⟩
  apply Manifold.IsImmersionAtOfComplement.mk_of_charts h.equiv d b hdx
    (hsource x hdx) (restr_mem_maximalAtlas _ h.domChart_mem_maximalAtlas hs) hb hsource
  intro v hv
  have hv' : v ∈ d.target := by simpa using hv
  have hdv := d.map_target hv'
  rw [hdsource] at hdv
  change h.codChart (φ (F (d.symm v))) = h.equiv (v, 0)
  rw [← heq hdv.2, hlift]
  apply h.writtenInCharts
  simpa using hv'.1




theorem exists_smooth_sphere_lift
    (q : UnitThreeSphere → M) (hq : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ q)
    (hcover : IsCoveringMap q)
    (f : UnitTwoSphere → M) (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (z₀ : UnitTwoSphere) (p₀ : UnitThreeSphere) (hp₀ : q p₀ = f z₀) :
    ∃ F : UnitTwoSphere → UnitThreeSphere,
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ F ∧
      F z₀ = p₀ ∧ ∀ z, q (F z) = f z := by
  let : SimplyConnectedSpace UnitTwoSphere := Poincare.Topology.standardSphereSimplyConnected 0
  let : LocallyPathConnectedSpace UnitTwoSphere :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) UnitTwoSphere
  obtain ⟨F, ⟨hF₀, hFq⟩, _⟩ := hcover.existsUnique_continuousMap_lifts
    ⟨f, hf.contMDiff.continuous⟩ z₀ p₀ hp₀
  have hlift (z : UnitTwoSphere) : q (F z) = f z := congrFun hFq z
  have hi := isImmersion_sphere_lift q hq hf.isImmersion F.continuous hlift
  have hinj : Function.Injective F := by
    intro x y hxy
    exact hf.isEmbedding.injective
      ((hlift x).symm.trans ((congrArg q hxy).trans (hlift y)))
  exact ⟨F, ⟨hi, (F.continuous.isClosedEmbedding hinj).isEmbedding⟩, hF₀, hlift⟩

end PoincareConjecture.M38

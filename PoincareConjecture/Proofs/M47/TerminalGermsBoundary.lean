import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v

namespace PoincareConjecture.M47



theorem terminalGerms_ball_subset_image
    {M : Type u} [TopologicalSpace M]
    {N : Type v} [TopologicalSpace N] [T2Space N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : RiemannianMetric 3 N) {U V : Set M} {f : M → N}
    (hf : Topology.IsOpenEmbedding (fun x : U => f x))
    (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hVU : closure V ⊆ U) {p : M} (hp : p ∈ V) {A : ℝ} (hA : 0 < A)
    (hboundary : ∀ x ∈ frontier V,
      ENNReal.ofReal A ≤ g.edist (f p) (f x)) :
    g.ball (f p) A ⊆ f '' V := by
  have hcont : ContinuousOn f U :=
    continuousOn_iff_continuous_domRestrict.mpr hf.continuous
  have himage : f '' V = (fun x : U => f x) '' (Subtype.val ⁻¹' V) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hVU (subset_closure hx)⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hopen : IsOpen (f '' V) := by
    rw [himage]
    exact hf.isOpenMap _ (hV.preimage continuous_subtype_val)
  have hclosed : IsClosed (f '' closure V) :=
    (hcompact.image_of_continuousOn (hcont.mono hVU)).isClosed
  have hclosure : closure (f '' V) ⊆ f '' closure V :=
    closure_minimal (image_mono subset_closure) hclosed
  apply (g.isPreconnected_ball (f p) A).subset_of_closure_inter_subset hopen
  · refine ⟨f p, ?_, mem_image_of_mem f hp⟩
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : N → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change g.edist (f p) (f p) < ENNReal.ofReal A
    simpa only [RiemannianMetric.edist, Manifold.riemannianEDist_self] using
      ENNReal.ofReal_pos.mpr hA
  · rintro y ⟨hyclosure, hyball⟩
    obtain ⟨x, hx, rfl⟩ := hclosure hyclosure
    have hxV : x ∈ V := by
      by_contra hxV
      have hfront : x ∈ frontier V := by
        rw [frontier, hV.interior_eq]
        exact ⟨hx, hxV⟩
      exact (not_lt_of_ge (hboundary x hfront)) hyball
    exact mem_image_of_mem f hxV

end PoincareConjecture.M47

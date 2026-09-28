import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.LocalDiffeomorphism








set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SmoothSpacetimeEmbedding

variable {n : ℕ} {T' T : ℝ} {C D : FlowCarrier n}
  {F : BasedFlow n T' T C} {G : BasedFlow n T' T D} {U : Set C.carrier}


noncomputable def spatialHomeomorph
    (e : SmoothSpacetimeEmbedding F G (Ioo T' T ×ˢ U))
    (hU : @IsOpen C.carrier C.topologicalSpace U) {t : ℝ} (ht : t ∈ Ioo T' T) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : TopologicalSpace D.carrier := D.topologicalSpace
    OpenPartialHomeomorph C.carrier D.carrier := by
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let : TopologicalSpace D.carrier := D.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) D.carrier := D.chartedSpace
  let : IsManifold (𝓡 n) ∞ D.carrier := D.isManifold
  let f := fun x => (e.toFun (t, x)).2
  let f' := fun y => (e.inverse (t, y)).2
  have hleft (x : C.carrier) (hx : x ∈ U) : f' (f x) = x := by
    have hp : e.toFun (t, x) = (t, f x) := Prod.ext (e.time_preserving t x) rfl
    simpa only [hp] using congrArg Prod.snd (e.left_inverse (t, x) ⟨ht, hx⟩)
  exact
    { toFun := f
      invFun := f'
      source := U
      target := f '' U
      map_source' := fun x hx => mem_image_of_mem f hx
      map_target' := by rintro _ ⟨x, hx, rfl⟩; simpa only [hleft x hx] using hx
      left_inv' := hleft
      right_inv' := by rintro _ ⟨x, hx, rfl⟩; rw [hleft x hx]
      open_source := hU
      open_target := e.spatialMap_isOpen_image hU ht
      continuousOn_toFun := fun x hx =>
        (e.spatialMap_contMDiffAt hU ht hx).continuousAt.continuousWithinAt
      continuousOn_invFun := by
        rintro _ ⟨x, hx, rfl⟩
        exact (e.spatialInverse_contMDiffAt hU ht hx).continuousAt.continuousWithinAt }

end PoincareConjecture.SmoothSpacetimeEmbedding

namespace PoincareConjecture.RiemannianMetric

theorem inverse_tangentNorm_le_of_le
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N) (he : e.MDifferentiable (𝓡 n) (𝓡 n))
    {V : Set M} (hV : V ⊆ e.source) {C : ℝ}
    (hbound : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ C * h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)) :
    ∀ y ∈ e '' V, ∀ v : TangentSpace (𝓡 n) y,
      g.tangentNorm (e.symm y) (mfderiv (𝓡 n) (𝓡 n) e.symm y v) ≤
        C * h.tangentNorm y v := by
  rintro _ ⟨x, hx, rfl⟩ v
  obtain ⟨w, hw⟩ := (he.mfderiv (hV hx)).surjective v
  change mfderiv (𝓡 n) (𝓡 n) e x w = v at hw
  have hback := congrArg (fun L => L w) (he.symm_comp_deriv (hV hx))
  change mfderiv (𝓡 n) (𝓡 n) e.symm (e x)
    (mfderiv (𝓡 n) (𝓡 n) e x w) = w at hback
  rw [← hw, hback, e.left_inv (hV hx)]
  exact hbound x hx w

end PoincareConjecture.RiemannianMetric

import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Circle.CompactArc
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Geometry.Manifold.Circle

private abbrev S1 := sphere (0 : EuclideanSpace Real (Fin 2)) 1




theorem exists_interval_parametrization_in_circle_of_injective_mfderiv
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] {I : ModelWithCorners Real E H} [IsManifold I ∞ M]
    {f : S1 -> M} (hf : ContMDiff (𝓡 1) I ∞ f)
    (hinj : Function.Injective f) (hder : ∀ q, Function.Injective (mfderiv (𝓡 1) I f q))
    {K : Set M} (hK : IsCompact K) (hconn : IsConnected K) (hKr : K ⊆ range f)
    {p : M} (hpr : p ∈ range f) (hp : p ∉ K) :
    ∃ (γ : Real -> M) (a b : Real),
      ContMDiff 𝓘(Real, Real) I ∞ γ ∧ Function.Injective γ ∧
      (∀ t, Function.Injective (mfderiv 𝓘(Real, Real) I γ t)) ∧
      a ≤ b ∧ γ '' Icc a b = K ∧ (K.Nontrivial → a < b) ∧
      range γ ⊆ range f ∧ Topology.IsEmbedding γ ∧ range γ = range f \ {p} := by
  have hfi := (hf.continuous.isClosedEmbedding hinj).isEmbedding
  obtain ⟨q, rfl⟩ := hpr
  have himage : f '' (f ⁻¹' K) = K := by
    rw [image_preimage_eq_inter_range, inter_eq_left.mpr hKr]
  have hcompact : IsCompact (f ⁻¹' K) :=
    (hK.isClosed.preimage hf.continuous).isCompact
  have hconnected : IsConnected (f ⁻¹' K) := by
    refine ⟨?_, hfi.isInducing.isPreconnected_image.mp ?_⟩
    · obtain ⟨x, hx⟩ := hconn.nonempty
      obtain ⟨y, rfl⟩ := hKr hx
      exact ⟨y, hx⟩
    · simpa only [himage] using hconn.isPreconnected
  obtain ⟨e, a, b, hes, het, he, hei, heinj, hab, hinterval, hstrict⟩ :=
    exists_interval_parametrization_of_compact_connected hcompact hconnected q hp
  have hed : e.MDifferentiable 𝓘(Real, Real) (𝓡 1) :=
    ⟨he.mdifferentiable (by simp) |>.mdifferentiableOn,
      hei.mdifferentiableOn (by simp)⟩
  refine ⟨f ∘ e, a, b, hf.comp he, hinj.comp heinj,
    ?_, hab, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [mfderiv_comp t (hf.mdifferentiable (by simp) (e t))
      (he.mdifferentiable (by simp) t)]
    exact (hder (e t)).comp (hed.mfderiv_injective (hes ▸ mem_univ t))
  · rw [image_comp, hinterval, himage]
  · intro hn
    exact hstrict (nontrivial_of_image f _ (by simpa only [himage] using hn))
  · rintro x ⟨t, rfl⟩
    exact ⟨e t, rfl⟩
  · exact hfi.comp (e.isOpenEmbedding hes).isEmbedding
  · ext y
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨⟨e t, rfl⟩, ?_⟩
      change f (e t) ≠ f q
      intro ht
      have hmem := e.map_source (hes ▸ mem_univ t)
      rw [het] at hmem
      exact hmem (hinj ht)
    · rintro ⟨⟨z, rfl⟩, hz⟩
      change f z ≠ f q at hz
      have hzt : z ∈ e.target := by
        rw [het]
        exact fun h => hz (congrArg f h)
      exact ⟨e.symm z, congrArg f (e.right_inv hzt)⟩


theorem exists_interval_parametrization_in_embedded_circle
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [TopologicalSpace H] [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] {I : ModelWithCorners Real E H} [IsManifold I ∞ M]
    {f : S1 -> M} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 1) I ∞ f)
    {K : Set M} (hK : IsCompact K) (hconn : IsConnected K) (hKr : K ⊆ range f)
    {p : M} (hpr : p ∈ range f) (hp : p ∉ K) :
    ∃ (γ : Real -> M) (a b : Real),
      ContMDiff 𝓘(Real, Real) I ∞ γ ∧ Function.Injective γ ∧
      (∀ t, Function.Injective (mfderiv 𝓘(Real, Real) I γ t)) ∧
      a ≤ b ∧ γ '' Icc a b = K ∧ (K.Nontrivial → a < b) ∧
      range γ ⊆ range f ∧ Topology.IsEmbedding γ ∧ range γ = range f \ {p} :=
  exists_interval_parametrization_in_circle_of_injective_mfderiv hf.contMDiff
    hf.isEmbedding.injective (fun q =>
      (hf.isImmersion.isImmersionAt q).injective_mfderiv_modelWithCornersSelf (by simp))
    hK hconn hKr hpr hp

end Poincare.Geometry.Manifold.Circle

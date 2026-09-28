import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E V : Type*} [TopologicalSpace M] [CompactSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_finite_triangulation_range_of_locallyPL
    {ι : Type*} (e : ι → OpenPartialHomeomorph M E) (F : M → V)
    (hFinj : Function.Injective F)
    (hcover : ∀ x : M, ∃ i, x ∈ (e i).source)
    (hFPL : ∀ i, LocallyPiecewiseAffineOn (F ∘ (e i).symm) (e i).target) :
    ∃ K : SimplicialComplex ℝ V, K.faces.Finite ∧ K.space = range F := by
  classical
  choose c hc using hcover
  choose L hL hxL hLt hFL using fun x =>
    hFPL (c x) (e (c x) x) ((e (c x)).mapsTo (hc x))
  have hlocalinj (x : M) : InjOn (F ∘ (e (c x)).symm) (L x).space := by
    intro y hy z hz hyz
    exact (e (c x)).symm.injOn (hLt x hy) (hLt x hz) (hFinj hyz)
  let J : M → SimplicialComplex ℝ V :=
    fun x => (hFL x).embeddedImage (hlocalinj x)
  have hJ (x : M) : (J x).faces.Finite :=
    (hFL x).embeddedImage_finite (hlocalinj x) (hL x)
  have hJs (x : M) : (J x).space = (F ∘ (e (c x)).symm) '' (L x).space :=
    (hFL x).embeddedImage_space (hlocalinj x)
  let U : M → Set M :=
    fun x => (e (c x)).source ∩ (e (c x)) ⁻¹' interior (L x).space
  have hU (x : M) : IsOpen (U x) :=
    (e (c x)).continuousOn.isOpen_inter_preimage (e (c x)).open_source isOpen_interior
  have hxU (x : M) : x ∈ U x := ⟨hc x, hxL x⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  obtain ⟨K, hK, hKs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion
    (fun x : t => J x) (fun x => hJ x)
  refine ⟨K, hK, hKs.trans ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := mem_iUnion.mp hz
    rw [hJs x] at hx
    obtain ⟨y, _, hy⟩ := hx
    exact ⟨(e (c x)).symm y, hy⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.mp (ht (mem_univ y))
    apply mem_iUnion.mpr
    refine ⟨⟨x, hxt⟩, ?_⟩
    rw [hJs x]
    refine ⟨e (c x) y, interior_subset hyU.2, ?_⟩
    change F ((e (c x)).symm (e (c x) y)) = F y
    rw [(e (c x)).left_inv hyU.1]

end OpenPartialHomeomorph

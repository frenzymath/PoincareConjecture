import PoincareConjecture.Proofs.M76.Mathlib.ConicalVertexMaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [DecidableEq E] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {f : E → F}

theorem AffineOnFaces.exists_cone_extension_affine (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite)
    (hlinK : ∀ r ∈ K.faces, LinearIndependent ℝ ((↑) : r → E))
    (hradK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ r ∈ (hf.embeddedImage hinj).faces, LinearIndependent ℝ ((↑) : r → F))
    (hradL : InjOn (NormedSpace.normalize : F → F) (hf.embeddedImage hinj).space) :
    ∃ g : E → F, ∃ e : (K.coneAtZero hlinK hradK).space ≃ₜ
        ((hf.embeddedImage hinj).coneAtZero hlinL hradL).space,
      (K.coneAtZero hlinK hradK).AffineOnFaces g ∧ g 0 = 0 ∧
        EqOn g f K.space ∧ ∀ x, (e x : F) = g x := by
  classical
  let L := hf.embeddedImage hinj
  have hzeroK : (0 : E) ∉ K.space := by
    intro h
    obtain ⟨r, hr, h0⟩ := mem_space_iff.mp h
    exact (hlinK r hr).zero_notMem_convexHull h0
  have hzeroL : (0 : F) ∉ L.space := by
    intro h
    obtain ⟨r, hr, h0⟩ := mem_space_iff.mp h
    exact (hlinL r hr).zero_notMem_convexHull h0
  let g := Function.invFunOn f K.space
  have hleft : LeftInvOn g f K.space := hinj.leftInvOn_invFunOn
  let v : E → F := fun x => if x = 0 then 0 else f x
  let w : F → E := fun y => if y = 0 then 0 else g y
  have hv (x : E) (hx : x ∈ K.space) : v x = f x := by
    dsimp only [v]
    rw [if_neg (fun h : x = 0 => hzeroK (h ▸ hx))]
  have hw (y : F) (hy : y ∈ L.space) : w y = g y := by
    dsimp only [w]
    rw [if_neg (fun h : y = 0 => hzeroL (h ▸ hy))]
  have hfv (x : E) (hx : x ∈ K.space) : f x ∈ L.space := by
    rw [hf.embeddedImage_space]
    exact mem_image_of_mem f hx
  have hvfaces : ∀ r ∈ K.faces, ∃ t ∈ L.faces, v '' (r : Set E) ⊆ (t : Set F) := by
    intro r hr
    refine ⟨r.image f, ?_, ?_⟩
    · rw [hf.embeddedImage_faces]
      exact mem_image_of_mem _ hr
    · rintro _ ⟨x, hx, rfl⟩
      rw [hv x (K.subset_space hr hx)]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hwfaces : ∀ t ∈ L.faces, ∃ r ∈ K.faces, w '' (t : Set F) ⊆ (r : Set E) := by
    intro t ht
    rw [hf.embeddedImage_faces] at ht
    obtain ⟨r, hr, rfl⟩ := ht
    refine ⟨r, hr, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [hw _ (hfv x (K.subset_space hr hx)), hleft (K.subset_space hr hx)]
    exact hx
  have hvw : LeftInvOn w v K.vertices := by
    intro x hx
    have hxK := vertices_subset_space hx
    rw [hv x hxK, hw _ (hfv x hxK), hleft hxK]
  have hwv : RightInvOn w v L.vertices := by
    intro y hy
    have hyL := vertices_subset_space hy
    have hyimage : y ∈ f '' K.space := (hf.embeddedImage_space hinj) ▸ hyL
    obtain ⟨x, hx, rfl⟩ := hyimage
    rw [hw _ hyL, hleft hx, hv x hx]
  obtain ⟨F, G, e, hF, _, hFv, _, he, _⟩ := K.exists_cone_homeomorph_of_vertex_maps L
    hK hlinK hradK hlinL hradL v w (by simp [v]) (by simp [w]) hvfaces hwfaces hvw hwv
  have hFbase : K.AffineOnFaces F := fun r hr => hF r (le_coneAtZero hlinK hradK hr)
  have heq : EqOn F f K.space := hFbase.eqOn_of_eqOn_vertices hf fun x hx =>
    (hFv (le_coneAtZero hlinK hradK hx)).trans (hv x (vertices_subset_space hx))
  refine ⟨F, e, hF, ?_, heq, he⟩
  exact (hFv (zero_mem_coneAtZero_vertices hlinK hradK)).trans (by simp [v])

theorem AffineOnFaces.exists_cone_extension (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite)
    (hlinK : ∀ r ∈ K.faces, LinearIndependent ℝ ((↑) : r → E))
    (hradK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ r ∈ (hf.embeddedImage hinj).faces, LinearIndependent ℝ ((↑) : r → F))
    (hradL : InjOn (NormedSpace.normalize : F → F) (hf.embeddedImage hinj).space) :
    ∃ e : (K.coneAtZero hlinK hradK).space ≃ₜ
        ((hf.embeddedImage hinj).coneAtZero hlinL hradL).space,
      e.IsFinitePL ∧ ∀ x : K.space,
        (e ⟨x, space_subset_of_le (le_coneAtZero hlinK hradK) x.property⟩ : F) = f x := by
  obtain ⟨g, e, hg, _, hbase, he⟩ :=
    hf.exists_cone_extension_affine hinj hK hlinK hradK hlinL hradL
  refine ⟨e, ⟨g, hg.finitePiecewiseAffineOn (finite_coneAtZero_faces hK hlinK hradK), he⟩, ?_⟩
  intro x
  exact (he ⟨x, space_subset_of_le (le_coneAtZero hlinK hradK) x.property⟩).trans
    (hbase x.property)

end Geometry.SimplicialComplex

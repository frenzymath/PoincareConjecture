import PoincareConjecture.Proofs.M76.Mathlib.ConicalAffineExtension
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseConeCarriers











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E}




theorem AffineOnFaces.smul_on_cone
    {hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E)}
    {hrad : InjOn (NormedSpace.normalize : E → E) K.space}
    {g : E → F} (hg : (K.coneAtZero hlin hrad).AffineOnFaces g) (hg0 : g 0 = 0)
    (x : E) (hx : x ∈ K.space) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
    g (r • x) = r • g x := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hg (insert 0 s) (insert_zero_mem_coneAtZero_faces hlin hrad hs)
  have h0 : (0 : E) ∈ convexHull ℝ ((insert 0 s : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_insert_self _ _)
  have hx' : x ∈ convexHull ℝ ((insert 0 s : Finset E) : Set E) :=
    convexHull_mono (Finset.subset_insert _ _) hxs
  have hrx : r • x ∈ convexHull ℝ ((insert 0 s : Finset E) : Set E) := by
    rw [Finset.coe_insert]
    exact smul_mem_convexHull_insert_zero hxs hr
  have ha0 : a 0 = 0 := (ha h0).symm.trans hg0
  have halinear (y : E) : a y = a.contLinear y := by
    have h := congrFun (a : E →ᵃ[ℝ] F).decomp y
    change a y = a.contLinear y + a 0 at h
    rwa [ha0, add_zero] at h
  calc
    g (r • x) = a (r • x) := ha hrx
    _ = r • a x := by rw [halinear, halinear, map_smul]
    _ = r • g x := congrArg (fun y => r • y) (ha hx').symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [DecidableEq F]
  {f : E → F}






theorem AffineOnFaces.exists_height_plane_preserving_cone_extension_affine
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hradK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ (hf.embeddedImage hinj).faces, LinearIndependent ℝ ((↑) : s → F))
    (hradL : InjOn (NormedSpace.normalize : F → F) (hf.embeddedImage hinj).space)
    (A : E →ₗ[ℝ] ℝ) (B C : F →ₗ[ℝ] ℝ)
    (hheight : ∀ x ∈ K.space, B (f x) = A x)
    {P : Set E} (hPK : P ⊆ K.space) (hPne : P.Nonempty)
    (hplane : ∀ x ∈ K.space, C (f x) = 0 ↔ x ∈ P) :
    ∃ e : (K.coneAtZero hlinK hradK).space ≃ₜ
        ((hf.embeddedImage hinj).coneAtZero hlinL hradL).space,
      e.IsFinitePL ∧
      (e ⟨0, vertices_subset_space (zero_mem_coneAtZero_vertices hlinK hradK)⟩ : F) = 0 ∧
      (∀ x, B (e x) = A x) ∧
      (∀ x, C (e x) = 0 ↔ (x : E) ∈ convexJoin ℝ {0} P) ∧
      (∀ x : K.space,
        (e ⟨x, space_subset_of_le (le_coneAtZero hlinK hradK) x.property⟩ : F) = f x) ∧
      ∃ g : E → F, (K.coneAtZero hlinK hradK).AffineOnFaces g ∧
        g 0 = 0 ∧ EqOn g f K.space ∧ ∀ x, (e x : F) = g x := by
  obtain ⟨g, e, hg, hg0, hbase, he⟩ :=
    hf.exists_cone_extension_affine hinj hK hlinK hradK hlinL hradL
  have hray (y : E) (hy : y ∈ K.space) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      g (r • y) = r • f y :=
    (hg.smul_on_cone hg0 y hy r hr).trans (congrArg (fun z => r • z) (hbase hy))
  have hcone := K.coneAtZero_space_eq_convexJoin hlinK hradK (hPne.mono hPK)
  have h0P : (0 : E) ∈ convexJoin ℝ {0} P :=
    subset_convexJoin_left hPne (mem_singleton 0)
  refine ⟨e, ⟨g, hg.finitePiecewiseAffineOn (finite_coneAtZero_faces hK hlinK hradK), he⟩,
    (he _).trans hg0, ?_, ?_, ?_, g, hg, hg0, hbase, he⟩
  · intro x
    obtain ⟨y, hy, r, hr, hxy⟩ :=
      (mem_convexJoin_zero_iff K.space (x : E)).mp (hcone ▸ x.property)
    rw [he, hxy, hray y hy r hr, map_smul, hheight y hy, map_smul]
  · intro x
    rw [he]
    constructor
    · intro hxC
      obtain ⟨y, hy, r, hr, hxy⟩ :=
        (mem_convexJoin_zero_iff K.space (x : E)).mp (hcone ▸ x.property)
      by_cases hr0 : r = 0
      · simpa only [hxy, hr0, zero_smul] using h0P
      · have hyC : C (f y) = 0 := by
          rw [hxy, hray y hy r hr, map_smul, smul_eq_mul] at hxC
          exact (mul_eq_zero.mp hxC).resolve_left hr0
        exact (mem_convexJoin_zero_iff P (x : E)).mpr
          ⟨y, (hplane y hy).mp hyC, r, hr, hxy⟩
    · intro hxP
      obtain ⟨y, hy, r, hr, hxy⟩ := (mem_convexJoin_zero_iff P (x : E)).mp hxP
      rw [hxy, hray y (hPK hy) r hr, map_smul, (hplane y (hPK hy)).mpr hy, smul_zero]
  · intro x
    exact (he _).trans (hbase x.property)






theorem AffineOnFaces.exists_height_plane_preserving_cone_extension
    (hf : K.AffineOnFaces f) (hinj : InjOn f K.space) (hK : K.faces.Finite)
    (hlinK : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (hradK : InjOn (NormedSpace.normalize : E → E) K.space)
    (hlinL : ∀ s ∈ (hf.embeddedImage hinj).faces, LinearIndependent ℝ ((↑) : s → F))
    (hradL : InjOn (NormedSpace.normalize : F → F) (hf.embeddedImage hinj).space)
    (A : E →ₗ[ℝ] ℝ) (B C : F →ₗ[ℝ] ℝ)
    (hheight : ∀ x ∈ K.space, B (f x) = A x)
    {P : Set E} (hPK : P ⊆ K.space) (hPne : P.Nonempty)
    (hplane : ∀ x ∈ K.space, C (f x) = 0 ↔ x ∈ P) :
    ∃ e : (K.coneAtZero hlinK hradK).space ≃ₜ
        ((hf.embeddedImage hinj).coneAtZero hlinL hradL).space,
      e.IsFinitePL ∧
      (e ⟨0, vertices_subset_space (zero_mem_coneAtZero_vertices hlinK hradK)⟩ : F) = 0 ∧
      (∀ x, B (e x) = A x) ∧
      (∀ x, C (e x) = 0 ↔ (x : E) ∈ convexJoin ℝ {0} P) ∧
      ∀ x : K.space,
        (e ⟨x, space_subset_of_le (le_coneAtZero hlinK hradK) x.property⟩ : F) = f x := by
  obtain ⟨e, he, he0, heheight, heplane, hebase, _⟩ :=
    hf.exists_height_plane_preserving_cone_extension_affine hinj hK hlinK hradK
      hlinL hradL A B C hheight hPK hPne hplane
  exact ⟨e, he, he0, heheight, heplane, hebase⟩

end Geometry.SimplicialComplex

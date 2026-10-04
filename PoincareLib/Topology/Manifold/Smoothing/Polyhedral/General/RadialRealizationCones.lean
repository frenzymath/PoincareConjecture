import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.IndependentRealization
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ConicalLinearProjection
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.BasisRadialProjection
import Mathlib.Data.Fintype.Powerset

/-!
# Geometric cones of labelled radial realizations

The actual geometric complexes underlying faithful radial vertex data
have conical carriers. A linear map preserving the vertex labels gives
a homeomorphism of these cones. This connects the operator coordinates
to the stars in Cairns 1940, pp. 799, 801; see M76 derivation 26.
-/

set_option autoImplicit false

open Set Geometry

namespace AbstractSimplicialComplex

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {A : AbstractSimplicialComplex ι}

/-- The geometric complex certified by a faithful radial realization.
Its faces are determined uniquely by the labelled data.
See Cairns p. 801 and M76 derivation 26. -/
noncomputable def RadialEmbedding.complex (v : A.RadialEmbedding E) :
    SimplicialComplex ℝ E := v.property.2.choose

/-- The realized complex has exactly the prescribed labelled faces.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_faces (v : A.RadialEmbedding E) :
    v.complex.faces = {t : Finset E | ∃ s ∈ A.faces, (t : Set E) = v.val '' (s : Set ι)} :=
  v.property.2.choose_spec.1

/-- Position vectors on every realized face are independent.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_linearIndependent (v : A.RadialEmbedding E) :
    ∀ s ∈ v.complex.faces, LinearIndependent ℝ ((↑) : s → E) :=
  v.property.2.choose_spec.2.1

/-- Central projection is injective on the realized link.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_injOn_normalize (v : A.RadialEmbedding E) :
    InjOn (NormedSpace.normalize : E → E) v.complex.space :=
  v.property.2.choose_spec.2.2

/-- Face images can equivalently be expressed as finite-set images.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_faces_image [DecidableEq E] (v : A.RadialEmbedding E) :
    v.complex.faces = (fun s : Finset ι => s.image v.val) '' A.faces := by
  rw [v.complex_faces]
  ext t
  constructor
  · rintro ⟨s, hs, he⟩
    exact ⟨s, hs, Finset.coe_injective (Finset.coe_image.trans he.symm)⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, Finset.coe_image⟩

/-- The realized vertices are exactly the labelled vertex range.
See Cairns p. 801 and M76 derivation 26. -/
theorem RadialEmbedding.complex_vertices (v : A.RadialEmbedding E) :
    v.complex.vertices = range v.val := by
  classical
  ext y
  change {y} ∈ v.complex.faces ↔ _
  rw [v.complex_faces_image]
  constructor
  · rintro ⟨s, _, he⟩
    dsimp only at he
    have hy : y ∈ s.image v.val := by rw [he]; simp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨{i}, A.singleton_mem i, by simp⟩

/-- Finite labels give a finite geometric complex.
See Cairns pp. 799, 801 and M76 derivation 26. -/
theorem RadialEmbedding.finite_complex_faces [Finite ι] (v : A.RadialEmbedding E) :
    v.complex.faces.Finite := by
  classical
  let := Fintype.ofFinite ι
  rw [v.complex_faces_image]
  exact (Set.toFinite A.faces).image _

/-- Cone the realized radial link to the origin.
See Cairns pp. 799, 801 and M76 derivation 26. -/
noncomputable def RadialEmbedding.cone (v : A.RadialEmbedding E) : SimplicialComplex ℝ E := by
  classical
  exact v.complex.coneAtZero v.complex_linearIndependent v.complex_injOn_normalize

/-- A vertex-compatible linear map restricts to a PL homeomorphism of
the two full cones. See Cairns p. 799 and M76 derivation 26. -/
theorem RadialEmbedding.exists_cone_homeomorph_of_linearMap [Finite ι]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (v : A.RadialEmbedding E) (w : A.RadialEmbedding F)
    (Q : E →L[ℝ] F) (hQ : ∀ i, Q (v.val i) = w.val i) :
    ∃ (g : F → E) (e : v.cone.space ≃ₜ w.cone.space),
      w.cone.AffineOnFaces g ∧ (∀ x : v.cone.space, (e x : F) = Q x) ∧
      (∀ y : w.cone.space, (e.symm y : E) = g y) := by
  classical
  apply v.complex.exists_cone_homeomorph_of_linear_map w.complex v.finite_complex_faces
    v.complex_linearIndependent v.complex_injOn_normalize
    w.complex_linearIndependent w.complex_injOn_normalize Q
  · intro x hx y hy he
    rw [v.complex_vertices] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    rw [hQ, hQ] at he
    exact congrArg v.val (w.property.1 he)
  · rw [v.complex_faces_image, w.complex_faces_image, Set.image_image]
    congr 1
    funext s
    rw [Finset.image_image]
    congr 1
    exact funext hQ |>.symm

/-- A vertex-compatible linear map is injective on the full cone.
See Cairns p. 799 and M76 derivation 26. -/
theorem RadialEmbedding.injOn_cone_of_linearMap [Finite ι]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (v : A.RadialEmbedding E) (w : A.RadialEmbedding F)
    (Q : E →L[ℝ] F) (hQ : ∀ i, Q (v.val i) = w.val i) : InjOn Q v.cone.space := by
  obtain ⟨_, e, _, he, _⟩ := v.exists_cone_homeomorph_of_linearMap w Q hQ
  intro x hx y hy hxy
  have hexy : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
    Subtype.ext ((he ⟨x, hx⟩).trans (hxy.trans (he ⟨y, hy⟩).symm))
  exact congrArg Subtype.val (e.injective hexy)

/-- A source basis is a faithful radial realization of any labelled
complex on the same index type. See Cairns p. 799 and M76 derivation 26. -/
noncomputable def basisRadialEmbedding (A : AbstractSimplicialComplex ι)
    (b : Module.Basis ι ℝ E) : A.RadialEmbedding E :=
  ⟨b, A.isRadialEmbedding_of_linearIndependent b.linearIndependent⟩

/-- A point of the operator-coordinate model is geometrically
injective on the cone of the source basis realization.
See Cairns p. 799 and M76 derivation 26. -/
theorem BasisRadialProjection.injOn_basisCone [Finite ι]
    [FiniteDimensional ℝ F] {b : Module.Basis ι ℝ E}
    (Q : A.BasisRadialProjection b F) : InjOn Q.val (A.basisRadialEmbedding b).cone.space := by
  let := b.finiteDimensional_of_finite
  exact (A.basisRadialEmbedding b).injOn_cone_of_linearMap
    ⟨fun i => Q.val (b i), Q.property⟩ Q.val (fun _ => rfl)

end AbstractSimplicialComplex

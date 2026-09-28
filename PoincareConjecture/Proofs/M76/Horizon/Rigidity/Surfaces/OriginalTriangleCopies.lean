import PoincareConjecture.Proofs.M76.Mathlib.FinitePLImageTriangulation











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E)

abbrev Triangle := {s : Finset E // s ∈ K.faces ∧ s.card = 3}

noncomputable def inclusion (a : ℝ) : E →ᴬ[ℝ] E × ℝ :=
  (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E a)

def copy (label : Triangle K → ℝ) (s : Triangle K) : Set (E × ℝ) :=
  inclusion (E := E) (label s) '' convexHull ℝ (s.val : Set E)

def carrier (label : Triangle K → ℝ) : Set (E × ℝ) := ⋃ s, copy K label s

theorem mem_copy_iff (label : Triangle K → ℝ) (s : Triangle K) (x : E × ℝ) :
    x ∈ copy K label s ↔ x.1 ∈ convexHull ℝ (s.val : Set E) ∧ x.2 = label s := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨hx, he⟩
    exact ⟨x.1, hx, Prod.ext rfl he.symm⟩

theorem disjoint_copies (label : Triangle K → ℝ) (hi : Function.Injective label)
    {s t : Triangle K} (hne : s ≠ t) : Disjoint (copy K label s) (copy K label t) := by
  apply Set.disjoint_left.mpr
  intro x hxs hxt
  exact hne (hi (((mem_copy_iff K label s x).mp hxs).2.symm.trans
    ((mem_copy_iff K label t x).mp hxt).2))

theorem projection_copy (label : Triangle K → ℝ) (s : Triangle K) :
    Prod.fst '' copy K label s = convexHull ℝ (s.val : Set E) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ((mem_copy_iff K label s y).mp hy).1
  · intro hx
    exact ⟨(x, label s), (mem_copy_iff K label s _).mpr ⟨hx, rfl⟩, rfl⟩

theorem projection_carrier (label : Triangle K → ℝ)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) :
    Prod.fst '' carrier K label = K.space := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, hs⟩ := mem_iUnion.mp hy
    exact K.convexHull_subset_space s.property.1 ((mem_copy_iff K label s y).mp hs).1
  · intro hx
    obtain ⟨s, hs, hxs⟩ := SimplicialComplex.mem_space_iff.mp hx
    obtain ⟨t, ht, hst, htc⟩ := hpure s hs
    let T : Triangle K := ⟨t, ht, htc⟩
    refine ⟨(x, label T), mem_iUnion.mpr ⟨T, ?_⟩, rfl⟩
    exact (mem_copy_iff K label T _).mpr
      ⟨convexHull_mono (Finset.coe_subset.mpr hst) hxs, rfl⟩

theorem collision_in_common_face (label : Triangle K → ℝ)
    {s t : Triangle K} {x y : E × ℝ}
    (hx : x ∈ copy K label s) (hy : y ∈ copy K label t) (he : x.1 = y.1) :
    x.1 ∈ convexHull ℝ ((s.val : Set E) ∩ (t.val : Set E)) := by
  classical
  exact K.inter_subset_convexHull s.property.1 t.property.1
    ⟨((mem_copy_iff K label s x).mp hx).1,
      he.symm ▸ ((mem_copy_iff K label t y).mp hy).1⟩

theorem projection_injective_on_copy (label : Triangle K → ℝ) (s : Triangle K) :
    InjOn Prod.fst (copy K label s) := by
  intro x hx y hy he
  exact Prod.ext he (((mem_copy_iff K label s x).mp hx).2.trans
    ((mem_copy_iff K label s y).mp hy).2.symm)

variable [FiniteDimensional ℝ E]

theorem exists_finite_triangulation (hK : K.faces.Finite) (label : Triangle K → ℝ) :
    ∃ J : SimplicialComplex ℝ (E × ℝ), J.faces.Finite ∧ J.space = carrier K label ∧
      J.AffineOnFaces Prod.fst := by
  classical
  let : Finite (Triangle K) :=
    (hK.subset (fun _ h ↦ h.1)).to_subtype
  obtain ⟨J, hJ, hJs, _⟩ := SimplicialComplex.exists_finite_triangulation_iUnion_finiteHull
    (fun s : Triangle K ↦ s.val.image (inclusion (E := E) (label s)))
  refine ⟨J, hJ, hJs.trans ?_, J.affineOnFaces_affine
    (ContinuousLinearMap.fst ℝ E ℝ).toContinuousAffineMap⟩
  apply iUnion_congr
  intro s
  rw [Finset.coe_image]
  exact (inclusion (E := E) (label s)).toAffineMap.image_convexHull (s.val : Set E) |>.symm

theorem finite_piecewise_affine_projection (hK : K.faces.Finite)
    (label : Triangle K → ℝ) :
    FinitePiecewiseAffineOn Prod.fst (carrier K label) := by
  obtain ⟨J, hJ, hJs, hproj⟩ := exists_finite_triangulation K hK label
  exact ⟨J, hJ, hJs, hproj⟩

theorem exists_separated_copies (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3) :
    ∃ (label : Triangle K → ℝ) (J : SimplicialComplex ℝ (E × ℝ)),
      Function.Injective label ∧ J.faces.Finite ∧ J.space = carrier K label ∧
      J.AffineOnFaces Prod.fst ∧ Prod.fst '' J.space = K.space := by
  classical
  let : Finite (Triangle K) := (hK.subset (fun _ h ↦ h.1)).to_subtype
  let : Fintype (Triangle K) := Fintype.ofFinite _
  let label : Triangle K → ℝ := fun s ↦ ((Fintype.equivFin (Triangle K) s).val : ℝ)
  have hi : Function.Injective label := by
    intro s t h
    apply (Fintype.equivFin (Triangle K)).injective
    apply Fin.ext
    exact Nat.cast_injective h
  obtain ⟨J, hJ, hJs, hproj⟩ := exists_finite_triangulation K hK label
  exact ⟨label, J, hi, hJ, hJs, hproj, hJs ▸ projection_carrier K label hpure⟩

end PoincareConjecture.M76.OriginalTriangleCopies

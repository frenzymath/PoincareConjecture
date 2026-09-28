import PoincareConjecture.Proofs.M76.Dehn.Mathlib.CompactPLDomainImage

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

variable {M E G : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem exists_local_polyhedral_image_pair
    {S B : Set M} {F : M → G} (hinj : InjOn F S)
    (T : OpenPartialHomeomorph M E)
    (hF : LocallyPiecewiseAffineOn (F ∘ T.symm) T.target)
    (cuts marks : Finset (E →ᵃ[ℝ] ℝ))
    {V : Set M} (hV : IsOpen V) (hVT : V ⊆ T.source)
    (hS : ∀ y ∈ V, y ∈ S ↔ ∀ a ∈ cuts, a (T y) ≤ 0)
    (hB : ∀ y ∈ V, y ∈ B ↔ ∀ a ∈ marks, a (T y) ≤ 0)
    {x : M} (hx : x ∈ V) :
    ∃ (U D : Set M) (K L : SimplicialComplex ℝ G),
      IsOpen U ∧ x ∈ U ∧ D ⊆ S ∧ U ∩ S ⊆ D ∧
      K.faces.Finite ∧ L.faces.Finite ∧
      K.space = F '' D ∧ L.space = F '' (D ∩ B) := by
  classical
  obtain ⟨J, hJ, hxJ, _, hFJ⟩ := hF (T x) (T.mapsTo (hVT hx))
  let W : Set E := T.target ∩ T.symm ⁻¹' V
  have hW : IsOpen W :=
    T.symm.continuousOn.isOpen_inter_preimage T.open_target hV
  have hxW : T x ∈ W := by
    exact ⟨T.mapsTo (hVT hx), by simpa only [mem_preimage, T.left_inv (hVT hx)] using hx⟩
  obtain ⟨J', hJ', hxJ', hJ'W, hFJ'⟩ := hFJ.exists_finite_neighborhood hJ
    (isCompact_singleton (x := T x)) hW (singleton_subset_iff.mpr ⟨hxJ, hxW⟩)
  let n := hJ'.toFinset.sup Finset.card
  have hn (s : Finset E) (hs : s ∈ J'.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hJ'.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨A, hA, hAJ, _, hcuts⟩ :=
    J'.exists_subdivision_respectsAffineHyperplanes hJ' hn (cuts ∪ marks)
  let P := A.affineHalfspaceSubcomplex cuts
  let Z := A.affineHalfspaceSubcomplex (cuts ∪ marks)
  have hP : P.faces.Finite := A.affineHalfspaceSubcomplex_finite cuts hA
  have hZ : Z.faces.Finite := A.affineHalfspaceSubcomplex_finite _ hA
  have hPs : P.space = A.space ∩ {z | ∀ a ∈ cuts, a z ≤ 0} :=
    A.affineHalfspaceSubcomplex_space cuts (fun a ha => hcuts a (Finset.mem_union_left _ ha))
  have hZs : Z.space = A.space ∩ {z | ∀ a ∈ cuts ∪ marks, a z ≤ 0} :=
    A.affineHalfspaceSubcomplex_space _ hcuts
  have hAt : A.space ⊆ T.target := by
    rw [hAJ.space_eq]
    exact fun _ hz => (hJ'W hz).2.1
  have hAV : MapsTo T.symm A.space V := by
    rw [hAJ.space_eq]
    exact fun _ hz => (hJ'W hz).2.2
  have hPA : P.space ⊆ A.space := hPs.subset.trans inter_subset_left
  have hZP : Z.space ⊆ P.space := by
    intro z hz
    rw [hZs] at hz
    rw [hPs]
    exact ⟨hz.1, fun a ha => hz.2 a (Finset.mem_union_left _ ha)⟩
  have hPS : MapsTo T.symm P.space S := by
    intro z hz
    apply (hS _ (hAV (hPA hz))).mpr
    rw [T.right_inv (hAt (hPA hz))]
    exact (hPs ▸ hz).2
  have hinjP : InjOn (F ∘ T.symm) P.space := by
    intro y hy z hz heq
    exact T.symm.injOn (hAt (hPA hy)) (hAt (hPA hz))
      (hinj (hPS hy) (hPS hz) heq)
  have hFA := hAJ.affineOnFaces hFJ'
  have hFP : P.AffineOnFaces (F ∘ T.symm) := fun s hs => hFA s hs.1
  have hFZ : Z.AffineOnFaces (F ∘ T.symm) := fun s hs => hFA s hs.1
  let D : Set M := T.symm '' P.space
  let U : Set M := T.source ∩ T ⁻¹' interior J'.space
  have hU : IsOpen U :=
    T.continuousOn.isOpen_inter_preimage T.open_source isOpen_interior
  have hUV : U ⊆ V := by
    intro y hy
    have hz := hAV (hAJ.space_eq.symm.subset (interior_subset hy.2))
    simpa only [T.left_inv hy.1] using hz
  have hUD : U ∩ S ⊆ D := by
    intro y hy
    refine ⟨T y, ?_, T.left_inv hy.1.1⟩
    rw [hPs, hAJ.space_eq]
    exact ⟨interior_subset hy.1.2, (hS y (hUV hy.1)).mp hy.2⟩
  have hDB : T.symm '' Z.space = D ∩ B := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨⟨z, hZP hz, rfl⟩, (hB _ (hAV (hPA (hZP hz)))).mpr ?_⟩
      rw [T.right_inv (hAt (hPA (hZP hz)))]
      exact fun a ha => (hZs ▸ hz).2 a (Finset.mem_union_right _ ha)
    · rintro ⟨⟨z, hz, rfl⟩, hb⟩
      refine ⟨z, ?_, rfl⟩
      have hb' := (hB _ (hAV (hPA hz))).mp hb
      rw [T.right_inv (hAt (hPA hz))] at hb'
      rw [hZs]
      refine ⟨hPA hz, fun a ha => ?_⟩
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (hPs ▸ hz).2 a ha
      · exact hb' a ha
  refine ⟨U, D, hFP.embeddedImage hinjP, hFZ.embeddedImage (hinjP.mono hZP),
    hU, ⟨hVT hx, hxJ' (mem_singleton _)⟩, ?_, hUD,
    hFP.embeddedImage_finite hinjP hP,
    hFZ.embeddedImage_finite (hinjP.mono hZP) hZ, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hPS hz
  · rw [hFP.embeddedImage_space]
    exact (image_image F T.symm P.space).symm
  · rw [hFZ.embeddedImage_space]
    exact (image_image F T.symm Z.space).symm.trans (congrArg (fun Q => F '' Q) hDB)

end PoincareConjecture.M76.HamiltonIntervalTorus

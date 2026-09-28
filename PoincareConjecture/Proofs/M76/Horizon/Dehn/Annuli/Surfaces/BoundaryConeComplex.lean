import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.BoundaryConeCaps
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.ConeFaces
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.ConeSurfaceCount
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Mathlib.EmbeddedSurfaceCount











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in


theorem exists_boundaryCircleCap_complex_with_faces (positive : Bool)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hne : K.space.Nonempty)
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) :
    ∃ C : SimplicialComplex ℝ (E × ℝ), C.faces.Finite ∧
      C.space = boundaryCircleCap positive K.space ∧
      (∀ s ∈ C.faces, s.card ≤ 3) ∧ C.surfaceEulerCount = 1 ∧
      (∀ s ∈ K.faces, s.image (fun x : E ↦ (x, (0 : ℝ))) ∈ C.faces) ∧
      (∀ s ∈ C.faces, (∀ x ∈ s, x.2 = 0) →
        ∃ t ∈ K.faces, s = t.image (fun x : E ↦ (x, (0 : ℝ)))) ∧
      ∀ s, s ∈ C.faces ↔
        (∃ t ∈ K.faces, s = t.image (fun x : E ↦ (x, (0 : ℝ)))) ∨
        s = {(0, capSign positive)} ∨
        ∃ t ∈ K.faces, s = insert (0, capSign positive)
          (t.image (fun x : E ↦ (x, (0 : ℝ)))) := by
  classical
  let hf := K.affineOnFaces_affine (circleLevelLift (E := E))
  have hi : InjOn (circleLevelLift : E → E × ℝ) K.space :=
    fun x _ y _ hxy ↦ congrArg Prod.fst hxy
  let J := hf.embeddedImage hi
  have hJ : J.faces.Finite := hf.embeddedImage_finite hi hK
  have hJs : J.space = circleLevelLift '' K.space := hf.embeddedImage_space hi
  have hJne : J.space.Nonempty := by rw [hJs]; exact hne.image _
  let ell : (E × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ E ℝ
  have hell (x : E × ℝ) (hx : x ∈ J.space) : ell x = 1 := by
    obtain ⟨y, hy, rfl⟩ := hJs.subset hx
    rfl
  let hlin := J.linearIndependent_faces_of_linear_level ell one_ne_zero hell
  let hrad := ell.injOn_normalize_of_level one_ne_zero hell
  let B := J.coneAtZero hlin hrad
  have hB : B.faces.Finite := SimplicialComplex.finite_coneAtZero_faces hJ hlin hrad
  have hBs : B.space = boundaryCircleCone K.space := by
    rw [J.coneAtZero_space_eq_convexJoin hlin hrad hJne, hJs]
    rfl
  have hdimJ : ∀ s ∈ J.faces, s.card ≤ 2 := by
    intro s hs
    rw [hf.embeddedImage_faces hi] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Finset.card_image_le.trans (hdim t ht)
  have hdimB : ∀ s ∈ B.faces, s.card ≤ 3 := by
    intro s hs
    have hs0 : (s.erase (0 : E × ℝ)).card ≤ 2 := by
      rcases hs.2 with hs | hs
      · rw [hs]; simp
      · exact hdimJ _ hs
    by_cases hz : (0 : E × ℝ) ∈ s
    · rw [Finset.card_erase_of_mem hz] at hs0
      have hpos := Finset.card_pos.mpr hs.1
      omega
    · rw [Finset.erase_eq_of_notMem hz] at hs0
      omega
  let hg := B.affineOnFaces_affine (capRebase (E := E) positive)
  let C := hg.embeddedImage (capRebase_injective positive).injOn
  have hcomposition (x : E) : capRebase positive (circleLevelLift x) = (x, (0 : ℝ)) := by
    apply Prod.ext
    · rfl
    · change capSign positive - capSign positive * 1 = 0
      ring
  refine ⟨C, hg.embeddedImage_finite _ hB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg.embeddedImage_space, hBs]
    rfl
  · intro s hs
    rw [hg.embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    exact Finset.card_image_le.trans (hdimB t ht)
  · rw [hg.surfaceEulerCount_embeddedImage]
    exact J.surfaceEulerCount_cone_eq_one hlin hrad hJ hdimJ
  · intro s hs
    rw [hg.embeddedImage_faces]
    have hsJ : s.image circleLevelLift ∈ J.faces := by
      rw [hf.embeddedImage_faces]
      exact ⟨s, hs, rfl⟩
    refine ⟨s.image circleLevelLift, J.le_coneAtZero hlin hrad hsJ, ?_⟩
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    exact hcomposition x
  · intro s hs hplane
    rw [hg.embeddedImage_faces] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have hzero : (0 : E × ℝ) ∉ t := by
      intro hz
      have hp := hplane (capRebase positive 0) (Finset.mem_image_of_mem _ hz)
      change capSign positive - capSign positive * 0 = 0 at hp
      cases positive <;> norm_num [capSign] at hp
    have htJ : t ∈ J.faces := by
      have hfaces := ht.2
      rw [Finset.erase_eq_of_notMem hzero] at hfaces
      exact hfaces.resolve_left ht.1.ne_empty
    rw [hf.embeddedImage_faces] at htJ
    obtain ⟨u, hu, rfl⟩ := htJ
    refine ⟨u, hu, ?_⟩
    simp only [Finset.image_image]
    apply Finset.image_congr
    intro x hx
    exact hcomposition x
  · intro s
    have hzero : capRebase positive (0 : E × ℝ) = (0, capSign positive) := by
      apply Prod.ext
      · rfl
      · change capSign positive - capSign positive * 0 = capSign positive
        ring
    have hbase (t : Finset E) :
        (t.image circleLevelLift).image (capRebase positive) =
          t.image (fun x : E ↦ (x, (0 : ℝ))) := by
      simp only [Finset.image_image]
      exact Finset.image_congr (fun x _ ↦ hcomposition x)
    rw [hg.embeddedImage_faces]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases (J.mem_coneAtZero_faces_cases hlin hrad t).mp ht with ht | rfl | ⟨u, hu, rfl⟩
      · rw [hf.embeddedImage_faces] at ht
        obtain ⟨u, hu, rfl⟩ := ht
        exact Or.inl ⟨u, hu, hbase u⟩
      · exact Or.inr (Or.inl (by simp only [Finset.image_singleton, hzero]))
      · rw [hf.embeddedImage_faces] at hu
        obtain ⟨a, ha, rfl⟩ := hu
        exact Or.inr (Or.inr ⟨a, ha, by simp only [Finset.image_insert, hzero, hbase]⟩)
    · rintro (⟨t, ht, rfl⟩ | rfl | ⟨t, ht, rfl⟩)
      · refine ⟨t.image circleLevelLift, J.le_coneAtZero hlin hrad ?_, hbase t⟩
        change t.image circleLevelLift ∈ (hf.embeddedImage hi).faces
        rw [hf.embeddedImage_faces]
        exact ⟨t, ht, rfl⟩
      · exact ⟨{0}, J.zero_mem_coneAtZero_vertices hlin hrad, by
          simp only [Finset.image_singleton, hzero]⟩
      · refine ⟨insert 0 (t.image circleLevelLift),
          SimplicialComplex.insert_zero_mem_coneAtZero_faces hlin hrad ?_, ?_⟩
        · rw [hf.embeddedImage_faces]
          exact ⟨t, ht, rfl⟩
        · simp only [Finset.image_insert, hzero, hbase]

open Classical in


theorem exists_boundaryCircleCap_complex (positive : Bool)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hne : K.space.Nonempty)
    (hdim : ∀ s ∈ K.faces, s.card ≤ 2) :
    ∃ C : SimplicialComplex ℝ (E × ℝ), C.faces.Finite ∧
      C.space = boundaryCircleCap positive K.space ∧
      (∀ s ∈ C.faces, s.card ≤ 3) ∧ C.surfaceEulerCount = 1 ∧
      (∀ s ∈ K.faces, s.image (fun x : E ↦ (x, (0 : ℝ))) ∈ C.faces) ∧
      ∀ s ∈ C.faces, (∀ x ∈ s, x.2 = 0) →
        ∃ t ∈ K.faces, s = t.image (fun x : E ↦ (x, (0 : ℝ))) := by
  obtain ⟨C, hC, hCs, hdimC, hcount, hbase, hplane, _⟩ :=
    exists_boundaryCircleCap_complex_with_faces positive K hK hne hdim
  exact ⟨C, hC, hCs, hdimC, hcount, hbase, hplane⟩
end PoincareConjecture.M76.Dehn.Annuli

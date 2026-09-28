import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Endpoint
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageReparameterization

set_option autoImplicit false
open Set Metric Geometry Topology unitInterval PLAnnularStrip

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun z : P2 => depth 8 z = -1 ∨ depth 8 z = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M} {s t : Stage e S f r C}
  {step : Step s t} {j : P2 → t.Carrier} {R Fmark : Set M}
  {a b : Ann} {W : Set s.Carrier} {ε : ℝ}
  (A : PlanarAnnulusBoundaryMotion step j R Fmark a b W ε)

theorem exists_moved_complexes :
    ∃ B K : SimplicialComplex ℝ V3,
      B.faces.Finite ∧ K.faces.Finite ∧ K ≤ B ∧ A.fixedRim ≤ K ∧
      B.faces = (fun face => face.image (A.motion.map 1)) '' A.branchComplex.faces ∧
      K.faces = (fun face => face.image (A.motion.map 1)) '' A.rimComplex.faces ∧
      K.vertices = A.motion.map 1 '' A.rimComplex.vertices ∧
      B.space = A.motion.map 1 '' A.source.space ∧
      K.space = A.motion.map 1 '' A.boundary.space ∧
      K.space = B.space ∩ {z | (A.coordinates z).1.1 = 0} ∧
      B.AffineOnFaces (A.parameter ∘ (A.motion.map 1).symm) ∧
      InjOn (A.parameter ∘ (A.motion.map 1).symm) B.space ∧
      MapsTo (A.parameter ∘ (A.motion.map 1).symm) B.space Ann ∧
      ∀ z ∈ B.space, z ∈ K.space ↔ (A.parameter ∘ (A.motion.map 1).symm) z ∈ Rim := by
  have hBaff : A.branchComplex.AffineOnFaces (A.motion.map 1) :=
    fun face hf => A.endpoint_affine face (A.branch_le hf)
  have hKaff : A.rimComplex.AffineOnFaces (A.motion.map 1) :=
    fun face hf => hBaff face (A.rim_le hf)
  have hiB : InjOn (A.motion.map 1) A.branchComplex.space := (A.motion.map 1).injective.injOn
  have hiK : InjOn (A.motion.map 1) A.rimComplex.space := (A.motion.map 1).injective.injOn
  let B := hBaff.embeddedImage hiB
  let K := hKaff.embeddedImage hiK
  have hB : B.faces.Finite := hBaff.embeddedImage_finite hiB (A.ambient_finite.subset A.branch_le)
  have hK : K.faces.Finite := hKaff.embeddedImage_finite hiK
    (A.ambient_finite.subset (A.rim_le.trans A.branch_le))
  have hKB : K ≤ B := by
    intro face hf
    change face ∈ (hKaff.embeddedImage hiK).faces at hf
    change face ∈ (hBaff.embeddedImage hiB).faces
    rw [hKaff.embeddedImage_faces hiK] at hf
    rw [hBaff.embeddedImage_faces hiB]
    obtain ⟨oldface, holdface, rfl⟩ := hf
    exact ⟨oldface, A.rim_le holdface, rfl⟩
  have hfix (z : V3) (hz : z ∈ A.fixedRim.space) : A.motion.map 1 z = z := by
    rcases (A.fixed_rim_space.subset hz).2 with hzC | hzfront
    · exact A.motion.fixed_protected 1 z hzC
    · exact A.motion.outside 1 z hzfront.2
  have hprotected : A.fixedRim ≤ K := hKaff.protected_le_embeddedImage hiK A.fixed_le hfix
  have hBs : B.space = A.motion.map 1 '' A.source.space := by
    rw [hBaff.embeddedImage_space hiB, A.branch_space]
  have hKs : K.space = A.motion.map 1 '' A.boundary.space := by
    rw [hKaff.embeddedImage_space hiK, A.rim_space]
  have hinv (z : V3) (hz : z ∈ B.space) : (A.motion.map 1).symm z ∈ A.source.space := by
    obtain ⟨x, hx, rfl⟩ := hBs.subset hz
    simpa only [(A.motion.map 1).symm_apply_apply] using hx
  have hlevel : K.space = B.space ∩ {z | (A.coordinates z).1.1 = 0} := by
    rw [hKs, hBs, A.boundary_level]
    ext z
    constructor
    · rintro ⟨x, ⟨hx, hx0⟩, rfl⟩
      exact ⟨mem_image_of_mem _ hx, (A.height 1 x).trans hx0⟩
    · rintro ⟨⟨x, hx, rfl⟩, hx0⟩
      exact ⟨x, ⟨hx, (A.height 1 x).symm.trans hx0⟩, rfl⟩
  have hleft : LeftInvOn (A.motion.map 1).symm (A.motion.map 1) A.branchComplex.space :=
    fun z _ => (A.motion.map 1).symm_apply_apply z
  have hparam := hBaff.comp_inverse_on_embeddedImage A.parameter_affine hiB hleft
  have hparami := hBaff.injOn_comp_inverse_on_embeddedImage hiB
    (A.parameter_injective.mono A.branch_space.subset) hleft
  refine ⟨B, K, hB, hK, hKB, hprotected, hBaff.embeddedImage_faces hiB,
    hKaff.embeddedImage_faces hiK, hKaff.embeddedImage_vertices hiK,
    hBs, hKs, hlevel, hparam, hparami,
    fun z hz => A.parameter_range (hinv z hz), ?_⟩
  intro z hz
  have hmem : z ∈ K.space ↔ (A.motion.map 1).symm z ∈ A.boundary.space := by
    rw [hKs]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [(A.motion.map 1).symm_apply_apply] using hx
    · intro h
      exact ⟨(A.motion.map 1).symm z, h, (A.motion.map 1).apply_symm_apply z⟩
  exact hmem.trans (A.parameter_rim _ (hinv z hz))

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

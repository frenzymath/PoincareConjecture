import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductTriangulation
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsFinitePL.exists_collar_base_restriction
    {B X : Set E} {T : Set F} {upper : E → ℝ} {β : ℝ} (hβ : 0 < β)
    (hupper : ∀ x ∈ B, upper x ≤ β)
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (hX : X ⊆ B)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hKX : K.space = X) :
    ∃ TX : Set F, TX ⊆ T ∧
      ∃ CX : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ TX,
        CX.IsFinitePL ∧
        (∀ p : {p : E × ℝ | p.1 ∈ X ∧ p.2 ∈ Icc 0 (upper p.1)},
          (CX p : F) = C ⟨p, hX p.property.1, p.property.2⟩) ∧
        ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
          (C p : F) ∈ TX ↔ (p : E × ℝ).1 ∈ X := by
  let D : Set (E × ℝ) := {p | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)}
  let DX : Set (E × ℝ) := {p | p.1 ∈ X ∧ p.2 ∈ Icc 0 (upper p.1)}
  have hDX : DX ⊆ D := fun _ hp => ⟨hX hp.1, hp.2⟩
  obtain ⟨f, hf, hval⟩ := hC
  have hcopy := hf
  obtain ⟨L, hL, hLD, _⟩ := hcopy
  have hI := isFinitePLBallPair_Icc hβ
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨J, hJ, hJI, _⟩, _⟩, _⟩ := hI
  obtain ⟨P, hP, hPs, _⟩ := K.exists_finite_triangulation_prod J hK hJ
  obtain ⟨W, hW, hWs⟩ := L.exists_finite_triangulation_inter P hL hP
  have hWX : W.space = DX := by
    rw [hWs, hLD, hPs, hKX, hJI]
    ext p
    constructor
    · exact fun hp => ⟨hp.2.1, hp.1.2⟩
    · intro hp
      exact ⟨hDX hp, hp.1, hp.2.1, hp.2.2.trans (hupper p.1 (hX hp.1))⟩
  have hfX : FinitePiecewiseAffineOn f DX :=
    hWX ▸ hf.restrict W hW (hWX.subset.trans hDX)
  have hinj : InjOn f D := by
    intro x hx y hy hxy
    have hCxy : C ⟨x, hx⟩ = C ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm)
    exact congrArg (fun z : D => (z : E × ℝ)) (C.injective hCxy)
  obtain ⟨CX, hCX, hCXval⟩ := hfX.exists_homeomorph_image (hinj.mono hDX)
  have hTX : f '' DX ⊆ T := by
    rintro y ⟨p, hp, rfl⟩
    rw [← hval ⟨p, hDX hp⟩]
    exact (C ⟨p, hDX hp⟩).property
  refine ⟨f '' DX, hTX, CX, hCX, ?_, ?_⟩
  · exact fun p => (hCXval p).trans (hval ⟨p, hDX p.property⟩).symm
  · intro p
    constructor
    · rintro ⟨x, hx, hxp⟩
      have heq : x = (p : E × ℝ) := hinj (hDX hx) p.property (hxp.trans (hval p))
      exact heq ▸ hx.1
    · exact fun hp => ⟨p, ⟨hp, p.property.2⟩, (hval p).symm⟩

end Homeomorph

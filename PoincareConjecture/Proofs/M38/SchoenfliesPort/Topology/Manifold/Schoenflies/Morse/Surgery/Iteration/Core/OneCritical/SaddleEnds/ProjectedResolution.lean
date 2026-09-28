import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneCritical.SaddleEnds.CutCircles
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Clearance

open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

open _root_.Poincare.Geometry.Manifold SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

variable {v : E3} {g : S2 → E3} {B : Set Real} {C : Set S2}

def lowerProjectedCutCircle (A : AnnularEndFamily v g B C)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (i : A.LowerCutIndex) (q : S1) : E2 :=
  planarProjection J (D (g (A.lowerCutCircle i q)))

def upperProjectedCutCircle (A : AnnularEndFamily v g B C)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (i : A.UpperCutIndex) (q : S1) : E2 :=
  planarProjection J (D (g (A.upperCutCircle i q)))

private theorem projected_circle_embedding_after_diffeomorph
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (s : S1 → S2) (hs : ContMDiff (𝓡 1) (𝓡 2) ∞ s) (hsi : Injective s)
    (hsd : ∀ q, Injective (mfderiv (𝓡 1) (𝓡 2) s q))
    {c : Real} (hh : ∀ q, inner Real v (g (s q)) = c) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun q => planarProjection J (D (g (s q)))) := by
  let G : S1 → E3 := D ∘ (g ∘ s)
  have hgs : ContMDiff (𝓡 1) (𝓡 3) ∞ (g ∘ s) := hg.contMDiff.comp hs
  have hG : ContMDiff (𝓡 1) (𝓡 3) ∞ G := D.contMDiff.comp hgs
  have hGheight (q : S1) : inner Real v (G q) = c :=
    (hDheight (g (s q))).trans (hh q)
  have hGi : Injective G := D.injective.comp (hg.isEmbedding.injective.comp hsi)
  have hgd (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) (g ∘ s) q) := by
    rw [mfderiv_comp q (hg.contMDiff.mdifferentiable (by simp) (s q))
      (hs.mdifferentiable (by simp) q)]
    exact (injective_mfderiv_sphere_embedding hg (s q)).comp (hsd q)
  have hGd (q : S1) : Injective (mfderiv (𝓡 1) (𝓡 3) G q) := by
    rw [show G = D ∘ (g ∘ s) from rfl,
      mfderiv_comp q (D.contMDiff.mdifferentiable (by simp) ((g ∘ s) q))
        (hgs.mdifferentiable (by simp) q)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) ((g ∘ s) q)).injective.comp (hgd q)
  let P : S1 → (Real ∙ v)ᗮ := fun q => (Real ∙ v)ᗮ.orthogonalProjectionOnto (G q)
  have hP : ContMDiff (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) ∞ P :=
    (Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp hG
  have hPi : Injective P := injective_projection_of_height_eq hv hGheight hGi
  have hPd (q : S1) : Injective (mfderiv (𝓡 1) 𝓘(Real, (Real ∙ v)ᗮ) P q) :=
    injective_mfderiv_projection_of_height_eq hv hG hGheight hGd q
  have hJ : ContMDiff 𝓘(Real, (Real ∙ v)ᗮ) (𝓡 2) ∞ J.symm.toContinuousLinearEquiv :=
    J.symm.toContinuousLinearEquiv.contDiff.contMDiff
  apply isSmoothEmbedding_of_injective_mfderiv (hJ.comp hP) (J.symm.injective.comp hPi)
  intro q
  change Injective (mfderiv (𝓡 1) (𝓡 2) (J.symm.toContinuousLinearEquiv ∘ P) q)
  rw [mfderiv_comp q (hJ.mdifferentiable (by simp) (P q)) (hP.mdifferentiable (by simp) q)]
  exact (J.symm.toContinuousLinearEquiv.toDiffeomorph.mfderivToContinuousLinearEquiv
    (by simp) (P q)).injective.comp (hPd q)

theorem lowerProjectedCutCircle_isSmoothEmbedding (A : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (i : A.LowerCutIndex) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (A.lowerProjectedCutCircle J D i) :=
  projected_circle_embedding_after_diffeomorph hg hv J D hDheight _
    (A.lowerCutCircle_geometry i).1 (A.lowerCutCircle_geometry i).2.1
    (A.lowerCutCircle_geometry i).2.2 (A.lowerCutCircle_height i)

theorem upperProjectedCutCircle_isSmoothEmbedding (A : AnnularEndFamily v g B C)
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y)
    (i : A.UpperCutIndex) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (A.upperProjectedCutCircle J D i) :=
  projected_circle_embedding_after_diffeomorph hg hv J D hDheight _
    (A.upperCutCircle_geometry i).1 (A.upperCutCircle_geometry i).2.1
    (A.upperCutCircle_geometry i).2.2 (A.upperCutCircle_height i)

theorem lowerProjectedCutCircle_joint_injective (A : AnnularEndFamily v g B C)
    (hg : Injective g) (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y) :
    Injective (fun z : A.LowerCutIndex × S1 => A.lowerProjectedCutCircle J D z.1 z.2) := by
  intro z y heq
  apply A.lowerCutCircle_joint_injective
  apply hg
  apply D.injective
  apply (Poincare.Geometry.Euclidean.heightCoordinates hv).symm.injective
  refine Prod.ext ?_ (J.symm.injective heq)
  exact ((hDheight _).trans (A.lowerCutCircle_height z.1 z.2)).trans
    ((hDheight _).trans (A.lowerCutCircle_height y.1 y.2)).symm

theorem upperProjectedCutCircle_joint_injective (A : AnnularEndFamily v g B C)
    (hg : Injective g) (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y) :
    Injective (fun z : A.UpperCutIndex × S1 => A.upperProjectedCutCircle J D z.1 z.2) := by
  intro z y heq
  apply A.upperCutCircle_joint_injective
  apply hg
  apply D.injective
  apply (Poincare.Geometry.Euclidean.heightCoordinates hv).symm.injective
  refine Prod.ext ?_ (J.symm.injective heq)
  exact ((hDheight _).trans (A.upperCutCircle_height z.1 z.2)).trans
    ((hDheight _).trans (A.upperCutCircle_height y.1 y.2)).symm

theorem lowerProjectedCutCircle_pairwise_disjoint (A : AnnularEndFamily v g B C)
    (hg : Injective g) (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y) :
    Pairwise (fun i j : A.LowerCutIndex => Disjoint (range (A.lowerProjectedCutCircle J D i))
      (range (A.lowerProjectedCutCircle J D j))) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨q, rfl⟩ ⟨z, he⟩
  have hjoint := A.lowerProjectedCutCircle_joint_injective hg hv J D hDheight
  have hh : (i, q) = (j, z) := hjoint (a₁ := (i, q)) (a₂ := (j, z)) he.symm
  exact hij (congrArg Prod.fst hh)

theorem upperProjectedCutCircle_pairwise_disjoint (A : AnnularEndFamily v g B C)
    (hg : Injective g) (hv : ‖v‖ = 1)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y : E3, inner Real v (D y) = inner Real v y) :
    Pairwise (fun i j : A.UpperCutIndex => Disjoint (range (A.upperProjectedCutCircle J D i))
      (range (A.upperProjectedCutCircle J D j))) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro x ⟨q, rfl⟩ ⟨z, he⟩
  have hjoint := A.upperProjectedCutCircle_joint_injective hg hv J D hDheight
  have hh : (i, q) = (j, z) := hjoint (a₁ := (i, q)) (a₂ := (j, z)) he.symm
  exact hij (congrArg Prod.fst hh)

theorem iUnion_range_lowerProjectedCutCircle (A : AnnularEndFamily v g B C)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    (⋃ i, range (A.lowerProjectedCutCircle J D i)) =
      (fun p : S2 => planarProjection J (D (g p))) ''
        {p | inner Real v (g p) = A.lowerCut} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hx
    exact ⟨A.lowerCutCircle i q, A.lowerCutCircle_height i q, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    rw [← A.iUnion_range_lowerCutCircle] at hp
    obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, q, rfl⟩

theorem iUnion_range_upperProjectedCutCircle (A : AnnularEndFamily v g B C)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) :
    (⋃ i, range (A.upperProjectedCutCircle J D i)) =
      (fun p : S2 => planarProjection J (D (g p))) ''
        {p | inner Real v (g p) = A.upperCut} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hx
    exact ⟨A.upperCutCircle i q, A.upperCutCircle_height i q, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    rw [← A.iUnion_range_upperCutCircle] at hp
    obtain ⟨i, q, rfl⟩ := mem_iUnion.mp hp
    exact mem_iUnion.mpr ⟨i, q, rfl⟩

theorem range_lowerProjectedCutCircle_pair (A : AnnularEndFamily v g B C)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (E : Fin 2 ≃ A.LowerCutIndex) :
    range (A.lowerProjectedCutCircle J D (E 0)) ∪ range (A.lowerProjectedCutCircle J D (E 1)) =
      (fun p : S2 => planarProjection J (D (g p))) ''
        {p | inner Real v (g p) = A.lowerCut} := by
  rw [← A.iUnion_range_lowerProjectedCutCircle J D]
  ext x
  constructor
  · rintro (hx | hx)
    · exact mem_iUnion.mpr ⟨E 0, hx⟩
    · exact mem_iUnion.mpr ⟨E 1, hx⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, rfl⟩ := E.surjective i
    fin_cases j
    · exact Or.inl hi
    · exact Or.inr hi

theorem range_upperProjectedCutCircle_pair (A : AnnularEndFamily v g B C)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (E : Fin 2 ≃ A.UpperCutIndex) :
    range (A.upperProjectedCutCircle J D (E 0)) ∪ range (A.upperProjectedCutCircle J D (E 1)) =
      (fun p : S2 => planarProjection J (D (g p))) ''
        {p | inner Real v (g p) = A.upperCut} := by
  rw [← A.iUnion_range_upperProjectedCutCircle J D]
  ext x
  constructor
  · rintro (hx | hx)
    · exact mem_iUnion.mpr ⟨E 0, hx⟩
    · exact mem_iUnion.mpr ⟨E 1, hx⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨j, rfl⟩ := E.surjective i
    fin_cases j
    · exact Or.inl hi
    · exact Or.inr hi

end Poincare.Manifold.Schoenflies.SphereSurgeryCoreCap.AnnularEndFamily

end

end M38Schoenflies

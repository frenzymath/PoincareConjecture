import PoincareConjecture.Proofs.M76.Rigidity.OriginalModelProduct
import PoincareConjecture.Proofs.M76.Rigidity.OriginalDiskParameterInverse
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBaseProductBall

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {j : V2 → X}
  {T : OriginalProperDiskTriangulation e R j}

open Classical in

theorem OriginalVertexProducts.exists_parameter_product (P : OriginalVertexProducts T) :
    ∃ k : V2 × ℝ → (T.index → ℝ × V3),
      FinitePiecewiseAffineOn k (D ×ˢ I) ∧ InjOn k (D ×ˢ I) ∧
      k '' (D ×ˢ I) =
        ⋃ p : (T.marked 2).vertices, T.dualRegion {(p : T.index → ℝ × V3)} ∧
      (∀ z ∈ D, (T.inverse (k (z, 0)) : X) = j z) ∧
      ∀ x ∈ D ×ˢ I, k x ∈ (T.marked 1).space ↔ x.1 ∈ Q := by
  classical
  let E := T.index → ℝ × V3
  obtain ⟨g, hg, hgi, hgimage, hgc, hgp⟩ := P.exists_model_product
  obtain ⟨b, hb, hbi, hbimage, _, hbcentral, hbproper⟩ := T.exists_disk_parameter_inverse
  have hbm : MapsTo b D (T.marked 2).space := fun z hz =>
    hbimage.subset ⟨z, hz, rfl⟩
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) I := by
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKI, _⟩, _⟩, _⟩ :=
      isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
    exact ⟨K, hK, hKI, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  let F : V2 × ℝ → E × ℝ := Prod.map b id
  have hF : MapsTo F (D ×ˢ I) ((T.marked 2).space ×ˢ I) :=
    fun x hx => ⟨hbm hx.1, hx.2⟩
  have hFimage : F '' (D ×ˢ I) = (T.marked 2).space ×ˢ I := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hF hx
    · rintro ⟨x, t⟩ ⟨hx, ht⟩
      obtain ⟨z, hz, hzx⟩ := hbimage.symm.subset hx
      refine ⟨(z, t), ⟨hz, ht⟩, ?_⟩
      exact Prod.ext hzx rfl
  refine ⟨g ∘ F, hg.comp (hb.prodMap hid) hF, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hFxy : F x = F y := hgi (hF hx) (hF hy) hxy
    exact Prod.ext (hbi hx.1 hy.1 (congrArg (fun z : E × ℝ => z.1) hFxy))
      (congrArg (fun z : E × ℝ => z.2) hFxy)
  · rw [Set.image_comp, hFimage, hgimage]
  · intro z hz
    change (T.inverse (g (b z, 0)) : X) = j z
    rw [hgc (b z) (hbm hz)]
    exact hbcentral z hz
  · intro x hx
    change g (F x) ∈ (T.marked 1).space ↔ x.1 ∈ Q
    rw [hgp (F x) (hF hx)]
    exact hbproper x.1 hx.1

end PoincareConjecture.M76

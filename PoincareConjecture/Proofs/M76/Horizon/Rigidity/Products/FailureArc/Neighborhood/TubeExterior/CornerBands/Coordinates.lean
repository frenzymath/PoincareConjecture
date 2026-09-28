import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.SourceBox
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_mul_sign (b : Bool) (x : ℝ) : sign b * (sign b * x) = x := by
  cases b <;> simp [sign]

noncomputable def arcMap (r : ℝ) (i : Bool × Bool) (s : ℝ) : P2 :=
  (sign i.1 * (r - max 0 s), sign i.2 * (r + s - max 0 s))

noncomputable def bandMap (r : ℝ) (i : Bool × Bool) (p : P2) : C3 :=
  (arcMap r i p.1, p.2)

def parameter (δ : ℝ) : Set P2 := Icc (-δ) δ ×ˢ Icc 0 1
def openParameter (δ : ℝ) : Set P2 := Ioo (-δ) δ ×ˢ Icc 0 1

def footprint (r δ : ℝ) (i : Bool × Bool) : Set P2 :=
  {z | (sign i.1 * z.1 ∈ Icc (r - δ) r) ∧
    (sign i.2 * z.2 ∈ Icc (r - δ) r) ∧
    (sign i.1 * z.1 = r ∨ sign i.2 * z.2 = r)}

def band (r δ : ℝ) (i : Bool × Bool) : Set C3 := footprint r δ i ×ˢ Icc 0 1

theorem signed_arcMap (r : ℝ) (i : Bool × Bool) (s : ℝ) :
    sign i.1 * (arcMap r i s).1 = r - max 0 s ∧
      sign i.2 * (arcMap r i s).2 = r + s - max 0 s := by
  simp [arcMap]

theorem arcMap_parameter (r : ℝ) (i : Bool × Bool) (s : ℝ) :
    sign i.2 * (arcMap r i s).2 - sign i.1 * (arcMap r i s).1 = s := by
  rw [(signed_arcMap r i s).1,(signed_arcMap r i s).2]
  ring

theorem arcMap_injective (r : ℝ) (i : Bool × Bool) : Function.Injective (arcMap r i) := by
  intro s t h
  simpa only [arcMap_parameter] using
    congrArg (fun z : P2 => sign i.2 * z.2 - sign i.1 * z.1) h

theorem bandMap_injective (r : ℝ) (i : Bool × Bool) : Function.Injective (bandMap r i) := by
  intro p q h
  apply Prod.ext (arcMap_injective r i (congrArg Prod.fst h))
  exact congrArg (fun z : C3 => z.2) h

@[simp] theorem arcMap_zero (r : ℝ) (i : Bool × Bool) :
    arcMap r i 0 = (sign i.1 * r,sign i.2 * r) := by
  simp [arcMap]

theorem arcMap_mem_footprint {r δ : ℝ} (hδ : 0 ≤ δ) (i : Bool × Bool)
    {s : ℝ} (hs : s ∈ Icc (-δ) δ) : arcMap r i s ∈ footprint r δ i := by
  change (_ ∈ Icc _ _) ∧ (_ ∈ Icc _ _) ∧ (_ = _ ∨ _ = _)
  rw [(signed_arcMap r i s).1,(signed_arcMap r i s).2]
  rcases le_total s 0 with h | h
  · rw [max_eq_left h]
    exact ⟨⟨by linarith,by linarith⟩,⟨by linarith [hs.1],by linarith⟩,Or.inl (by ring)⟩
  · rw [max_eq_right h]
    exact ⟨⟨by linarith [hs.2],by linarith⟩,⟨by linarith,by linarith⟩,Or.inr (by ring)⟩

theorem arcMap_inverse {r δ : ℝ} {i : Bool × Bool} {z : P2}
    (hz : z ∈ footprint r δ i) :
    arcMap r i (sign i.2 * z.2 - sign i.1 * z.1) = z := by
  have h₁ : sign i.1 * z.1 ≤ r := hz.1.2
  have h₂ : sign i.2 * z.2 ≤ r := hz.2.1.2
  apply Prod.ext
  · change sign i.1 * (r - max 0 (sign i.2 * z.2 - sign i.1 * z.1)) = z.1
    rcases hz.2.2 with h | h
    · rw [max_eq_left (by linarith)]
      simpa only [sub_zero,← h] using sign_mul_sign i.1 z.1
    · rw [max_eq_right (by linarith)]
      have heq : r - (sign i.2 * z.2 - sign i.1 * z.1) = sign i.1 * z.1 := by linarith
      rw [heq,sign_mul_sign]
  · change sign i.2 * (r + (sign i.2 * z.2 - sign i.1 * z.1) -
      max 0 (sign i.2 * z.2 - sign i.1 * z.1)) = z.2
    rcases hz.2.2 with h | h
    · rw [max_eq_left (by linarith)]
      have heq : r + (sign i.2 * z.2 - sign i.1 * z.1) - 0 = sign i.2 * z.2 := by linarith
      rw [heq,sign_mul_sign]
    · rw [max_eq_right (by linarith)]
      have heq : r + (sign i.2 * z.2 - sign i.1 * z.1) -
          (sign i.2 * z.2 - sign i.1 * z.1) = sign i.2 * z.2 := by linarith
      rw [heq,sign_mul_sign]

theorem arcMap_image {r δ : ℝ} (hδ : 0 ≤ δ) (i : Bool × Bool) :
    arcMap r i '' Icc (-δ) δ = footprint r δ i := by
  apply Subset.antisymm
  · rintro _ ⟨s,hs,rfl⟩
    exact arcMap_mem_footprint hδ i hs
  · intro z hz
    exact ⟨sign i.2 * z.2 - sign i.1 * z.1,
      ⟨by linarith [hz.1.2,hz.2.1.1],by linarith [hz.1.1,hz.2.1.2]⟩,
      arcMap_inverse hz⟩

theorem bandMap_image {r δ : ℝ} (hδ : 0 ≤ δ) (i : Bool × Bool) :
    bandMap r i '' parameter δ = band r δ i := by
  change Prod.map (arcMap r i) id '' (Icc (-δ) δ ×ˢ Icc 0 1) = _
  rw [prodMap_image_prod,image_id,arcMap_image hδ]
  rfl

theorem bandMap_finitePL (r : ℝ) {δ : ℝ} (hδ : 0 < δ) (i : Bool × Bool) :
    FinitePiecewiseAffineOn (bandMap r i) (parameter δ) := by
  have hball := (isFinitePLBallPair_Icc (show -δ < δ by linarith)).prod
    (isFinitePLBallPair_Icc (by norm_num : (0 : ℝ) < 1))
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ := hball
  have ha (a : P2 →ᴬ[ℝ] ℝ) : FinitePiecewiseAffineOn a (parameter δ) :=
    ⟨K,hK,hKs,K.affineOnFaces_affine a⟩
  have hs := ha (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  have ht := ha (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap
  have hr := ha (ContinuousAffineMap.const ℝ P2 r)
  have hx := (hr.sub hs.positivePart).postcomp
    (sign i.1 • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
  have hy := ((hr.add hs).sub hs.positivePart).postcomp
    (sign i.2 • ContinuousLinearMap.id ℝ ℝ).toContinuousAffineMap
  exact (hx.prod_mk hy).prod_mk ht

end PoincareConjecture.M76.Dehn.Annuli.TubeExterior.CornerBands

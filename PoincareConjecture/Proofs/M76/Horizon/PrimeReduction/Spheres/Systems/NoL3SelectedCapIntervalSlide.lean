import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLUnionMaps



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem exists_selected_cap_interval_slide {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Icc (-ε) ε ≃ₜ Icc (-ε) ε,
      H.IsFinitePL ∧
      (∀ t : Icc (-ε) ε, (H t : ℝ) =
        if (t : ℝ) ≤ 0 then (3 * (t : ℝ) + ε) / 2 else ((t : ℝ) + ε) / 2) ∧
      (H ⟨-ε,by constructor <;> linarith⟩ : ℝ) = -ε ∧
      (H ⟨ε,by constructor <;> linarith⟩ : ℝ) = ε ∧
      (H ⟨0,by constructor <;> linarith⟩ : ℝ) = ε / 2 ∧
      ∀ t : Icc (-ε) ε, (H t : ℝ) ≤ ε / 2 ↔ (t : ℝ) ≤ 0 := by
  classical
  let φ : ℝ → ℝ := fun t => if t ≤ 0 then (3*t+ε)/2 else (t+ε)/2
  let ψ : ℝ → ℝ := fun t => if t ≤ ε/2 then (2*t-ε)/3 else 2*t-ε
  let A : ℝ →ᴬ[ℝ] ℝ :=
    (3/2 : ℝ) • (ContinuousAffineMap.id ℝ ℝ) + ContinuousAffineMap.const ℝ ℝ (ε/2)
  let B : ℝ →ᴬ[ℝ] ℝ :=
    (1/2 : ℝ) • (ContinuousAffineMap.id ℝ ℝ) + ContinuousAffineMap.const ℝ ℝ (ε/2)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨K,hK,hKs,_⟩,_⟩,_⟩ :=
    isFinitePLBallPair_Icc (show -ε < 0 by linarith)
  obtain ⟨_,_,_,_,_,_,⟨_,⟨L,hL,hLs,_⟩,_⟩,_⟩ := isFinitePLBallPair_Icc hε
  have hA : FinitePiecewiseAffineOn φ (Icc (-ε) 0) := by
    have ha : FinitePiecewiseAffineOn A (Icc (-ε) 0) :=
      ⟨K,hK,hKs,K.affineOnFaces_affine A⟩
    exact ha.congr (fun t ht => by dsimp [A,φ]; rw [if_pos ht.2]; ring)
  have hB : FinitePiecewiseAffineOn φ (Icc 0 ε) := by
    have hb : FinitePiecewiseAffineOn B (Icc 0 ε) :=
      ⟨L,hL,hLs,L.affineOnFaces_affine B⟩
    apply hb.congr
    intro t ht
    dsimp [B,φ]
    split_ifs with ht0
    · have : t = 0 := le_antisymm ht0 ht.1
      subst t
      ring
    · ring
  have hcover : Icc (-ε) 0 ∪ Icc 0 ε = Icc (-ε) ε := by
    ext t
    simp only [mem_union,mem_Icc]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1,h.2]
    · intro ht
      rcases le_total t 0 with h | h
      · exact Or.inl ⟨ht.1,h⟩
      · exact Or.inr ⟨h,ht.2⟩
  have hφ : FinitePiecewiseAffineOn φ (Icc (-ε) ε) :=
    hcover ▸ finitePiecewiseAffineOn_union hA hB
  have hφmap : MapsTo φ (Icc (-ε) ε) (Icc (-ε) ε) := by
    intro t ht
    dsimp [φ]
    split_ifs with ht0 <;> constructor <;> linarith [ht.1,ht.2]
  have hψmap : MapsTo ψ (Icc (-ε) ε) (Icc (-ε) ε) := by
    intro t ht
    dsimp [ψ]
    split_ifs with ht0 <;> constructor <;> linarith [ht.1,ht.2]
  have hleft (t : ℝ) : ψ (φ t) = t := by
    by_cases ht : t ≤ 0
    · have hval : φ t = (3*t+ε)/2 := if_pos ht
      have hsmall : φ t ≤ ε/2 := by rw [hval]; linarith
      change (if φ t ≤ ε/2 then (2*φ t-ε)/3 else 2*φ t-ε) = t
      rw [if_pos hsmall,hval]
      ring
    · have hval : φ t = (t+ε)/2 := if_neg ht
      have hlarge : ¬φ t ≤ ε/2 := by rw [hval]; linarith
      change (if φ t ≤ ε/2 then (2*φ t-ε)/3 else 2*φ t-ε) = t
      rw [if_neg hlarge,hval]
      ring
  have hright (t : ℝ) : φ (ψ t) = t := by
    by_cases ht : t ≤ ε/2
    · have hval : ψ t = (2*t-ε)/3 := if_pos ht
      have hsmall : ψ t ≤ 0 := by rw [hval]; linarith
      change (if ψ t ≤ 0 then (3*ψ t+ε)/2 else (ψ t+ε)/2) = t
      rw [if_pos hsmall,hval]
      ring
    · have hval : ψ t = 2*t-ε := if_neg ht
      have hlarge : ¬ψ t ≤ 0 := by rw [hval]; linarith
      change (if ψ t ≤ 0 then (3*ψ t+ε)/2 else (ψ t+ε)/2) = t
      rw [if_neg hlarge,hval]
      ring
  have hφinj : InjOn φ (Icc (-ε) ε) := by
    intro x _ y _ hxy
    simpa only [hleft] using congrArg ψ hxy
  obtain ⟨H,hH,hHval⟩ := hφ.exists_homeomorph_image hφinj
  have himage : φ '' Icc (-ε) ε = Icc (-ε) ε := by
    apply Subset.antisymm (image_subset_iff.mpr hφmap)
    intro t ht
    exact ⟨ψ t,hψmap ht,hright t⟩
  let H' := H.trans (Homeomorph.setCongr himage)
  have hH' : H'.IsFinitePL := hH.setCongr rfl himage
  have hv (t : Icc (-ε) ε) : (H' t : ℝ) = φ t := hHval t
  refine ⟨H',hH',hv,?_,?_,?_,?_⟩
  · rw [hv]
    dsimp [φ]
    rw [if_pos (by linarith)]
    ring
  · rw [hv]
    dsimp [φ]
    rw [if_neg (not_le.mpr hε)]
    ring
  · rw [hv]
    simp [φ]
  · intro t
    rw [hv]
    dsimp [φ]
    split_ifs with ht <;> constructor <;> intro h <;> linarith

end PoincareConjecture.M76

import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Attachments.CylinderGluing



set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "Cyl" => Set.prod Q (Icc (-1 : ℝ) 1)

theorem exists_cylinder_reversal :
    ∃ J : Cyl ≃ₜ Cyl, J.IsFinitePL ∧ ∀ x, (J x : V2 × ℝ) = (x.val.1, -x.val.2) := by
  let f : (V2 × ℝ) →ᴬ[ℝ] (V2 × ℝ) :=
    (ContinuousLinearMap.fst ℝ V2 ℝ).toContinuousAffineMap.prod
      (-(ContinuousLinearMap.snd ℝ V2 ℝ).toContinuousAffineMap)
  have hfv (x : V2 × ℝ) : f x = (x.1, -x.2) := rfl
  have hfmap : MapsTo f Cyl Cyl := by
    intro x hx
    exact ⟨hx.1, by change -1 ≤ -x.2 ∧ -x.2 ≤ 1; constructor <;> linarith [hx.2.1, hx.2.2]⟩
  have hff (x : V2 × ℝ) : f (f x) = x := by rw [hfv, hfv]; simp
  have hfi : Function.Injective f := fun _ _ h ↦
    (hff _).symm.trans ((congrArg f h).trans (hff _))
  obtain ⟨K, hK, hKs⟩ := exists_finite_unitCubeSphere (ι := Fin 2)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (-1 : ℝ) < 1 by norm_num)
  have hqid : FinitePiecewiseAffineOn (id : V2 → V2) Q :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ V2)⟩
  have hiid : FinitePiecewiseAffineOn (id : ℝ → ℝ) (Icc (-1 : ℝ) 1) :=
    ⟨L, hL, hLs, L.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have hid : FinitePiecewiseAffineOn (id : V2 × ℝ → V2 × ℝ) Cyl := hqid.prodMap hiid
  have hf : FinitePiecewiseAffineOn f Cyl := hid.postcomp f
  have himage : f '' Cyl = Cyl := by
    apply Subset.antisymm (image_subset_iff.mpr hfmap)
    intro x hx
    exact ⟨f x, hfmap hx, hff x⟩
  obtain ⟨J, hJ, hJv⟩ := hf.exists_homeomorph_image hfi.injOn
  exact ⟨J.trans (Homeomorph.setCongr himage), hJ.setCongr rfl himage,
    fun x ↦ (hJv x).trans (hfv x)⟩

end PoincareConjecture.M76.Dehn.Annuli

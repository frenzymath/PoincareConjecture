import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeJointOriginalCollar
import PoincareConjecture.Proofs.M76.Triangulation.ZeroChargeAffineHeightStep

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.ZeroChargeJoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

theorem exists_paired_step_of_original_polygon_collar
    (hdim : Module.finrank ℝ E = 3)
    {S C T : Set E} (hCcv : Convex ℝ C) (hSC : S ⊆ interior C)
    (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) {c r tau : ℝ}
    (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPinj : Function.Injective P) (hsection : P.boundary ℝ = S ∩ {x | A x = c})
    (hr : 0 < r) (htau : 0 < tau)
    (G : (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r) :
      Set (E × (ℝ × ℝ))) ≃ₜ T) (hG : G.IsFinitePL)
    (hGheight : ∀ p, A (G p) = c + (p : E × (ℝ × ℝ)).2.1)
    (hGsurface : ∀ p, (G p : E) ∈ S ↔ (p : E × (ℝ × ℝ)).2.2 = 0)
    (hGcore : ∀ p : (P.boundary ℝ ×ˢ (Icc (-r) r ×ˢ Icc (-r) r) :
      Set (E × (ℝ × ℝ))), (p : E × (ℝ × ℝ)).2 = 0 → (G p : E) = (p : E × (ℝ × ℝ)).1)
    (hband : S ∩ {x | |A x - c| ≤ tau} ⊆ T)
    (disks : ℝ → Set E)
    (hdisks : ∀ t ∈ Icc (-tau) tau,
      IsFinitePLBallPair (ℝ × ℝ) (disks (c + t)) (S ∩ {y | A y = c + t}) ∧
        disks (c + t) ⊆ {y | A y = c + t}) :
    ∃ δ : ℝ, 0 < δ ∧ δ < tau ∧
      ∀ a b : ℝ, |a - c| ≤ δ → |b - c| ≤ δ → a ≤ b →
        HasPairedHeightCap S C (disks a) A a →
          HasPairedHeightCap S C (disks b) A b := by
  obtain ⟨h, hh, hhinv⟩ := exists_affine_height_coordinates (E := ℝ × ℝ) A hA
    (by simp [Module.finrank_prod, hdim]) c
  let pi : E →ᴬ[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap.comp
      h.symm.toContinuousAffineMap
  have hzero : (0 : ℝ) ∈ Icc (-tau) tau := ⟨neg_nonpos.mpr htau.le, htau.le⟩
  have hd0 := hdisks 0 hzero
  simp only [add_zero] at hd0
  have hpiBack (y : E) (hy : A y = c) : h (pi y, 0) = y := by
    have hy0 : (h.symm y).2 = 0 := by rw [hhinv, hy, sub_self]
    have hp : (pi y, (0 : ℝ)) = h.symm y := Prod.ext rfl hy0.symm
    rw [hp, h.apply_symm_apply]
  have hpiinj : InjOn pi {y | A y = c} := by
    intro x hx y hy hxy
    rw [← hpiBack x hx, ← hpiBack y hy, hxy]
  let d : Set (ℝ × ℝ) := pi '' disks c
  let q : Set (ℝ × ℝ) := pi '' P.boundary ℝ
  have hd : IsFinitePLBallPair (ℝ × ℝ) d q := by
    have hh := hd0.1.affine_image pi (hpiinj.mono hd0.2)
    rwa [← hsection] at hh
  let B := A - AffineMap.const ℝ E c
  have hB : B.linear ≠ 0 := by simpa [B] using hA
  have hdP : IsFinitePLBallPair (ℝ × ℝ) (disks c) (P.boundary ℝ) := by
    simpa only [hsection] using hd0.1
  have hdplane : disks c ⊆ {y | B y = 0} := by
    intro y hy
    change A y - c = 0
    exact sub_eq_zero.mpr (hd0.2 hy)
  have hdC : disks c ⊆ interior C :=
    hdP.subset_convex_of_planar_polygon_boundary P hP hPinj B hB hdim
      hdplane hCcv.interior (fun y hy => by
        obtain ⟨i, rfl⟩ := hy
        exact hSC ((hsection.subset (P.vertex_mem_boundary i)).1))
  have hdCnorm : ∀ x ∈ d, h (x, (0 : ℝ)) ∈ interior C := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hpiBack y (hd0.2 hy)]
    exact hdC hy
  obtain ⟨epsilon, hepsilon, K, hK, hKcv, hdK, _, e, he, heheight,
      hestart, hesurface, hesmallband⟩ :=
    exists_joint_cylinder_of_original_polygon_collar P hP hPinj
      (by simp [Module.finrank_prod]) hr htau A h hh G hG hGheight hGsurface
      hGcore hband hd.isCompact
  have hepsTau : epsilon < tau := hepsilon.2.trans_le (min_le_right _ _)
  have hsmallband : S ∩ {y | A y - c ∈ Icc (-epsilon) epsilon} ⊆
      h '' (K.space ×ˢ Icc (-epsilon) epsilon) := by
    intro y hy
    refine ⟨h.symm y, hesmallband ⟨?_, ?_⟩, h.apply_symm_apply y⟩
    · change h (h.symm y) ∈ S
      simpa only [h.apply_symm_apply] using hy.1
    · change (h.symm y).2 ∈ Icc (-epsilon) epsilon
      rw [hhinv]
      exact hy.2
  have hsmallDisks : ∀ t ∈ Icc (-epsilon) epsilon,
      IsFinitePLBallPair (ℝ × ℝ) (disks (c + t)) (S ∩ {y | A y = c + t}) ∧
        disks (c + t) ⊆ {y | A y = c + t} := by
    intro t ht
    apply hdisks t
    exact ⟨(neg_le_neg hepsTau.le).trans ht.1, ht.2.trans hepsTau.le⟩
  obtain ⟨δ, hδ, hδε, hstep⟩ := exists_affine_paired_height_cap_step
    K hK hKcv hepsilon.1 e he heheight hestart h A hA hdim hh hd hdK
      hdCnorm hesurface hsmallband disks hsmallDisks
  exact ⟨δ, hδ, hδε.trans hepsTau, hstep⟩

end PoincareConjecture.M76.ZeroChargeJoint

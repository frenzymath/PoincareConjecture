import PoincareConjecture.Proofs.M76.Mathlib.TriangleSegmentSideTransport











set_option autoImplicit false

open Set CoordinateHalfBoxes

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]







theorem exists_actual_cut_pole_filling_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : s.card = 3)
    {a p : E} (ha : a ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (f : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E) (hfzero : f 0 = a)
    {r : ℝ} (hr : 0 < r)
    (hsurface : ∀ x ∈ box r, f x ∈ K.space ↔ x.2 = 0)
    (e : E ≃L[ℝ] ((ℝ × ℝ) × ℝ))
    (hlast : ∀ x : (ℝ × ℝ) × ℝ, (e (f x)).2 = x.2)
    (ψ : (ℝ × ℝ) → E) (hψ : Continuous ψ) (hψzero : ψ 0 = p)
    (hψlast : ∀ x : ℝ × ℝ, (e (ψ x)).2 = x.2)
    (A : E →ₗ[ℝ] ℝ) (hA : A ≠ 0) (hdim : Module.finrank ℝ E = 3)
    (hheight : ∀ x, A (f x) = x.1.1) (hψheight : ∀ x, A (ψ x) = x.1)
    {d : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d (K.space ∩ {x | A x = 0}))
    (hdplane : d ⊆ {x | A x = 0})
    (hinward : ∀ x ∈ box r, x.1.1 = 0 → (f x ∈ d ↔ 0 ≤ x.2)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧
      ∀ z : ℝ, |z| ≤ δ → (ψ (0, z) ∈ d ↔ 0 ≤ z) := by
  let u : ℝ → E := fun z => f ((0, 0), z)
  let v : ℝ → E := fun z => ψ (0, z)
  have hu : Continuous u := f.continuous.comp (continuous_const.prodMk continuous_id)
  have hv : Continuous v := hψ.comp (continuous_const.prodMk continuous_id)
  have hu0 : u 0 = a := hfzero
  have hv0 : v 0 = p := hψzero
  let C : E →ₗ[ℝ] ℝ := (LinearMap.snd ℝ (ℝ × ℝ) ℝ).comp e.toLinearMap
  have hplane : ∀ x : E, x ∈ affineSpan ℝ (s : Set E) ↔ C x = 0 :=
    K.mem_triangle_affineSpan_iff_last_eq_zero_of_cut_box
      hK hbound hs hcard ha f hfzero hr hsurface e hlast
  obtain ⟨ε, hε, htransport⟩ :=
    K.exists_uniform_planar_disk_side_transport hK hbound hs hcard u v hu hv
      (hu0.symm ▸ ha) (hv0.symm ▸ hp) C hplane
      (fun z => hlast ((0, 0), z)) (fun z => hψlast (0, z))
      hd A.toAffineMap hA hdim hdplane inter_subset_left
      (fun z => hheight ((0, 0), z)) (fun z => hψheight (0, z))
  let δ := min ε r / 2
  have hmin : 0 < min ε r := lt_min hε hr
  have hδ : 0 < δ := half_pos hmin
  have hδε : δ < ε := (half_lt_self hmin).trans_le (min_le_left _ _)
  have hδr : δ ≤ r := (half_lt_self hmin).le.trans (min_le_right _ _)
  refine ⟨δ, hδ, hδr, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    have hpK : p ∈ K.space := K.convexHull_subset_space hs (intrinsicInterior_subset hp)
    have hpA : A p = 0 := by
      have h := hψheight (0 : ℝ × ℝ)
      change A (ψ 0) = 0 at h
      rwa [hψzero] at h
    have hpd : ψ (0, (0 : ℝ)) ∈ d := by
      change ψ 0 ∈ d
      rw [hψzero]
      exact hd.1 ⟨hpK, hpA⟩
    exact ⟨fun _ => le_rfl, fun _ => hpd⟩
  · have hzbox : ((0, 0), z) ∈ box r := by
      exact ⟨⟨⟨neg_nonpos.mpr hr.le, hr.le⟩, neg_nonpos.mpr hr.le, hr.le⟩,
        abs_le.mp (hz.trans hδr)⟩
    exact (htransport z (hz.trans_lt hδε) hz0).symm.trans
      (hinward ((0, 0), z) hzbox rfl)

end Geometry.SimplicialComplex

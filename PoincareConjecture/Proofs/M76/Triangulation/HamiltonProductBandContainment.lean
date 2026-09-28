import PoincareConjecture.Proofs.M76.Triangulation.HamiltonUnmarkedDiskProduct
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperProductOpenness
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1
local notation "I" => Icc (-(1 / 4 : ℝ)) (1 / 4)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_prescribed_band_width {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b) (a : E ≃ᴬ[ℝ] V3)
    (hR : PLDomain
      (fun _ : Unit => (Homeomorph.refl V3).toOpenPartialHomeomorph) (a '' R))
    (F : (V2 × ℝ) → E) (hF : FinitePiecewiseAffineOn F (Q2 ×ˢ I))
    (hFfront : MapsTo F (Q2 ×ˢ I) (frontier R))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0)) :
    ∃ w : ℝ, 0 < w ∧ w ≤ 1 / 8 ∧
      MapsTo F (Q2 ×ˢ Icc (-w) w)
        (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)) := by
  have hopen := isOpen_image_proper_finitePL_product a hR
    zero_lt_one P.map P.piecewiseAffine P.injective P.inside P.proper
  have hRclosed : IsClosed R := by
    have h := hR.closed.preimage a.continuous
    simpa only [preimage_image_eq _ a.injective] using h
  let i0 : I := ⟨0, by norm_num⟩
  let f : Q2 × I → R := fun p => ⟨F ((p.1 : V2), (p.2 : ℝ)),
    hRclosed.frontier_subset (hFfront ⟨p.1.property, p.2.property⟩)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact hF.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨p.1.property, p.2.property⟩)
  let U := f ⁻¹' ((Subtype.val : R → E) ⁻¹'
    (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)))
  have hU : IsOpen U := hopen.preimage hf
  have hbase : (univ : Set Q2) ×ˢ {i0} ⊆ U := by
    rintro ⟨x, t⟩ ⟨_, ht⟩
    have ht' : t = i0 := ht
    subst t
    change F ((x : V2), 0) ∈ P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1)
    rw [hcenter x x.property]
    exact mem_image_of_mem P.map ⟨sphere_subset_closedBall x.property, by norm_num⟩
  let : CompactSpace Q2 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V2) 1)
  obtain ⟨u, v, _, hv, hu, h0v, huv⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hU hbase
  obtain ⟨r, hr, hrv⟩ := Metric.isOpen_iff.mp hv i0 (h0v (mem_singleton i0))
  let w := min (r / 2) (1 / 8 : ℝ)
  have hw : 0 < w := lt_min (half_pos hr) (by norm_num)
  have hwr : w < r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hwsmall : w ≤ (1 / 8 : ℝ) := min_le_right _ _
  refine ⟨w, hw, hwsmall, ?_⟩
  intro p hp
  have htI : p.2 ∈ I := ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  let t : I := ⟨p.2, htI⟩
  have htv : t ∈ v := hrv (by
    change dist p.2 (0 : ℝ) < r
    rw [Real.dist_eq, sub_zero]
    exact (abs_le.mpr hp.2).trans_lt hwr)
  have h := huv (show ((⟨p.1, hp.1⟩ : Q2), t) ∈ u ×ˢ v from
    ⟨hu (mem_univ _), htv⟩)
  exact h

theorem exists_prescribed_band_coordinates {R D : Set E} {b : D2 ≃ₜ D}
    (P : HamiltonUnmarkedDiskProduct R b)
    (F : (V2 × ℝ) → E)
    (hFinj : InjOn F (Q2 ×ˢ I))
    (hFfront : MapsTo F (Q2 ×ˢ I) (frontier R))
    (hcenter : ∀ x ∈ Q2, F (x, 0) = P.map (x, 0))
    {w : ℝ} (hwsmall : w ≤ 1 / 4)
    (hband : MapsTo F (Q2 ×ˢ Icc (-w) w)
      (P.map '' (D2 ×ˢ Ioo (-1 : ℝ) 1))) :
    ∃ j : E → (V2 × ℝ),
      FinitePiecewiseAffineOn j (P.map '' (D2 ×ˢ Icc (-1 : ℝ) 1)) ∧
      (∀ p ∈ D2 ×ˢ Icc (-1 : ℝ) 1, j (P.map p) = p) ∧
      (∀ y ∈ P.map '' (D2 ×ˢ Icc (-1 : ℝ) 1), P.map (j y) = y) ∧
      (∀ p ∈ Q2 ×ˢ Icc (-w) w, j (F p) ∈ Q2 ×ˢ Ioo (-1 : ℝ) 1) ∧
      (∀ x ∈ Q2, j (F (x, 0)) = (x, 0)) ∧
      ∀ p ∈ Q2 ×ˢ Icc (-w) w, (j (F p)).2 = 0 ↔ p.2 = 0 := by
  obtain ⟨H, hH, hHv⟩ := P.piecewiseAffine.exists_homeomorph_image P.injective
  obtain ⟨j, hj, hjv⟩ := hH.symm
  have hjP (p : V2 × ℝ) (hp : p ∈ D2 ×ˢ Icc (-1 : ℝ) 1) :
      j (P.map p) = p := by
    rw [← hHv ⟨p, hp⟩, ← hjv, H.symm_apply_apply]
  have hPj (y : E) (hy : y ∈ P.map '' (D2 ×ˢ Icc (-1 : ℝ) 1)) :
      P.map (j y) = y := by
    rw [← hjv ⟨y, hy⟩, ← hHv, H.apply_symm_apply]
  have hsmall : Q2 ×ˢ Icc (-w) w ⊆ Q2 ×ˢ I := fun p hp =>
    ⟨hp.1, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
  have hcoord (p : V2 × ℝ) (hp : p ∈ Q2 ×ˢ Icc (-w) w) :
      j (F p) ∈ Q2 ×ˢ Ioo (-1 : ℝ) 1 := by
    obtain ⟨z, hz, hfz⟩ := hband hp
    have hzC : z ∈ D2 ×ˢ Icc (-1 : ℝ) 1 := ⟨hz.1, Ioo_subset_Icc_self hz.2⟩
    rw [← hfz, hjP z hzC]
    exact ⟨(P.proper z hzC).mp (hfz.symm ▸ hFfront (hsmall hp)), hz.2⟩
  have hzero (x : V2) (hx : x ∈ Q2) : j (F (x, 0)) = (x, 0) := by
    rw [hcenter x hx]
    exact hjP (x, 0) ⟨sphere_subset_closedBall hx, by norm_num⟩
  refine ⟨j, hj, hjP, hPj, hcoord, hzero, ?_⟩
  intro p hp
  constructor
  · intro hz
    have hc := hcoord p hp
    have hFp : F p ∈ P.map '' (D2 ×ˢ Icc (-1 : ℝ) 1) :=
      image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self) (hband hp)
    have hFc : F ((j (F p)).1, 0) = F p := by
      rw [hcenter _ hc.1]
      have he : ((j (F p)).1, (0 : ℝ)) = j (F p) := by
        apply Prod.ext
        · rfl
        · exact hz.symm
      rw [he]
      exact hPj _ hFp
    have he := hFinj (show ((j (F p)).1, (0 : ℝ)) ∈ Q2 ×ˢ I from
      ⟨hc.1, by norm_num⟩) (hsmall hp) hFc
    exact (congrArg Prod.snd he).symm
  · intro ht
    have he : p = (p.1, (0 : ℝ)) := Prod.ext rfl ht
    rw [he, hzero p.1 hp.1]

end PoincareConjecture.M76.HamiltonIndexOne

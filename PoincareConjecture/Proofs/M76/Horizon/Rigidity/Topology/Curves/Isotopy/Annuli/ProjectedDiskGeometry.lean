import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.Support

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))

noncomputable def annularLiftProjectionAt (c : ℝ) (x : P2) : P2 :=
  annulusMap 8 (by norm_num) (((c + x.2 : ℝ) : Circle), x.1)

@[simp] theorem annularLiftProjectionAt_zero : annularLiftProjectionAt 0 = annularLiftProjection := by
  funext x
  simp [annularLiftProjectionAt, annularLiftProjection]

theorem annularLiftProjectionAt_period (c : ℝ) (x : P2) (k : ℤ) :
    annularLiftProjectionAt c (x + (0, 32 * (k : ℝ))) = annularLiftProjectionAt c x := by
  have hp : ((32 * (k : ℝ) : ℝ) : Circle) = 0 :=
    (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨k, by simp [zsmul_eq_mul]; ring⟩
  simp only [annularLiftProjectionAt, Prod.fst_add, Prod.snd_add, add_zero,
    ← add_assoc, AddCircle.coe_add, hp]

theorem annularLiftProjection_period (x : P2) (k : ℤ) :
    annularLiftProjection (x + (0, 32 * (k : ℝ))) = annularLiftProjection x := by
  have hp : ((32 * (k : ℝ) : ℝ) : Circle) = 0 :=
    (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mpr ⟨k, by simp [zsmul_eq_mul]; ring⟩
  simp only [annularLiftProjection, Prod.fst_add, Prod.snd_add, add_zero,
    AddCircle.coe_add, hp]

theorem finitePL_annularLiftProjectionAt (c : ℝ)
    (K : SimplicialComplex ℝ P2) (hK : K.faces.Finite)
    (hheight : ∀ x ∈ K.space, x.1 ∈ Ioo (-1 : ℝ) 1) :
    FinitePiecewiseAffineOn (annularLiftProjectionAt c) K.space := by
  let s : P2 →ᴬ[ℝ] P2 :=
    ((ContinuousAffineMap.const ℝ P2 c) + (ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap
  have hswap : FinitePiecewiseAffineOn s K.space := by
    exact (K.affineOnFaces_affine s).finitePiecewiseAffineOn hK
  have hs (x : P2) : s x = (c + x.2, x.1) := rfl
  have hcomp :=
    (locallyPiecewiseAffineOn_annulusMap_lift (L := 8) (d := 1)
      (by norm_num) (by norm_num) (by norm_num)).comp_finitePiecewiseAffineOn hswap
      (by
        intro x hx
        rw [hs]
        exact ⟨mem_univ _, hheight x hx⟩)
  apply hcomp.congr
  intro x hx
  change annulusMap 8 (by norm_num) (((s x).1 : Circle), (s x).2) =
    annulusMap 8 (by norm_num) (((c + x.2 : ℝ) : Circle), x.1)
  rw [hs]

theorem injOn_annularLiftProjectionAt_strip (c : ℝ) {a b : ℝ}
    (hwidth : b - a < 32) :
    InjOn (annularLiftProjectionAt c) (Icc (-1 : ℝ) 1 ×ˢ Icc a b) := by
    let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
    intro x hx' y hy' heq
    have h := injective_annulusMap (L := 8) (d := 1) (by norm_num) (by norm_num)
      (a₁ := (((c + x.2 : ℝ) : Circle), ⟨x.1, hx'.1⟩))
      (a₂ := (((c + y.2 : ℝ) : Circle), ⟨y.1, hy'.1⟩)) heq
    have hheight := congrArg (fun z : Circle × Icc (-1 : ℝ) 1 => (z.2 : ℝ)) h
    have hphase : (x.2 : Circle) = (y.2 : Circle) := by
      have hh := congrArg Prod.fst h
      change ((c + x.2 : ℝ) : Circle) = ((c + y.2 : ℝ) : Circle) at hh
      simpa only [AddCircle.coe_add, add_left_cancel_iff] using hh
    exact Prod.ext hheight ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show x.2 ∈ Ico a (a + 4 * (8 : ℝ)) from ⟨hx'.2.1, by linarith [hx'.2.2]⟩)
      (show y.2 ∈ Ico a (a + 4 * (8 : ℝ)) from ⟨hy'.2.1, by linarith [hy'.2.2]⟩)).mp hphase)

theorem annularLiftProjectionAt_fiber (c : ℝ) {x y : P2}
    (hx : x.1 ∈ Icc (-1 : ℝ) 1) (hy : y.1 ∈ Icc (-1 : ℝ) 1) :
    annularLiftProjectionAt c x = annularLiftProjectionAt c y ↔
      ∃ k : ℤ, x = y + (0, 32 * (k : ℝ)) := by
  constructor
  · intro heq
    have h := injective_annulusMap (L := 8) (d := 1) (by norm_num) (by norm_num)
      (a₁ := (((c + x.2 : ℝ) : Circle), ⟨x.1, hx⟩))
      (a₂ := (((c + y.2 : ℝ) : Circle), ⟨y.1, hy⟩)) heq
    have hh := congrArg (fun z : Circle × Icc (-1 : ℝ) 1 => (z.2 : ℝ)) h
    have hp : (x.2 : Circle) = (y.2 : Circle) := by
      have h' := congrArg Prod.fst h
      change ((c + x.2 : ℝ) : Circle) = ((c + y.2 : ℝ) : Circle) at h'
      simpa only [AddCircle.coe_add, add_left_cancel_iff] using h'
    have hz : ((x.2 - y.2 : ℝ) : Circle) = 0 := by rw [AddCircle.coe_sub, hp, sub_self]
    obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (4 * (8 : ℝ))).mp hz
    refine ⟨k, Prod.ext ?_ ?_⟩
    · simpa only [Prod.fst_add, add_zero] using hh
    · change x.2 = y.2 + 32 * (k : ℝ)
      simp only [zsmul_eq_mul] at hk
      linarith
  · rintro ⟨k, rfl⟩
    exact annularLiftProjectionAt_period c y k

theorem exists_finitePL_projected_annular_disk_at (c : ℝ)
    {D : Set P2} {a b : ℝ}
    (hD : IsFinitePLBallPair P2 D (frontier D)) (hwidth : b - a < 32)
    (hstrip : D ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc a b) :
    FinitePiecewiseAffineOn (annularLiftProjectionAt c) D ∧ InjOn (annularLiftProjectionAt c) D ∧
    IsFinitePLBallPair P2 (annularLiftProjectionAt c '' D) (frontier (annularLiftProjectionAt c '' D)) ∧
    annularLiftProjectionAt c '' frontier D = frontier (annularLiftProjectionAt c '' D) ∧
    annularLiftProjectionAt c '' D ⊆ depth 8 ⁻¹' Ioo (-1 : ℝ) 1 ∧
    ∃ Q : D ≃ₜ (annularLiftProjectionAt c '' D), Q.IsFinitePL ∧
      ∀ x : D, (Q x : P2) = annularLiftProjectionAt c x := by
  have hDcopy := hD
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hDcopy
  have hp : FinitePiecewiseAffineOn (annularLiftProjectionAt c) D := hKs ▸
    finitePL_annularLiftProjectionAt c K hK (fun x hx => (hstrip (hKs ▸ hx)).1)
  have hi : InjOn (annularLiftProjectionAt c) D := by
    apply (injOn_annularLiftProjectionAt_strip c hwidth).mono
    intro x hx
    exact ⟨⟨(hstrip hx).1.1.le, (hstrip hx).1.2.le⟩, (hstrip hx).2⟩
  have himage := hD.image hp hi
  have hfront := himage.frontier_eq_of_finrank_eq rfl
  obtain ⟨Q, hQ, hQv⟩ := hp.exists_homeomorph_image hi
  refine ⟨hp, hi, hfront.symm ▸ himage, hfront.symm, ?_, Q, hQ, hQv⟩
  rintro _ ⟨x, hx, rfl⟩
  change depth 8 (annulusMap 8 _ (((c + x.2 : ℝ) : Circle), x.1)) ∈ Ioo (-1 : ℝ) 1
  rw [depth_annulusMap (by norm_num) (by
    have hh := abs_le.mpr ⟨(hstrip hx).1.1.le, (hstrip hx).1.2.le⟩
    linarith)]
  exact (hstrip hx).1

theorem exists_finitePL_projected_annular_disk
    {D : Set P2} {a b : ℝ}
    (hD : IsFinitePLBallPair P2 D (frontier D)) (hwidth : b - a < 32)
    (hstrip : D ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc a b) :
    FinitePiecewiseAffineOn annularLiftProjection D ∧ InjOn annularLiftProjection D ∧
    IsFinitePLBallPair P2 (annularLiftProjection '' D) (frontier (annularLiftProjection '' D)) ∧
    annularLiftProjection '' frontier D = frontier (annularLiftProjection '' D) ∧
    annularLiftProjection '' D ⊆ depth 8 ⁻¹' Ioo (-1 : ℝ) 1 ∧
    ∃ Q : D ≃ₜ (annularLiftProjection '' D), Q.IsFinitePL ∧
      ∀ x : D, (Q x : P2) = annularLiftProjection x := by
  have h := exists_finitePL_projected_annular_disk_at 0 hD hwidth hstrip
  rw [annularLiftProjectionAt_zero] at h
  exact h

end PoincareConjecture.M76.Dehn

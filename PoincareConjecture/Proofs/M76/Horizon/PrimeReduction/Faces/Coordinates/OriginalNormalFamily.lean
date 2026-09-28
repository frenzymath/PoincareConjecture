import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.Coordinates.OriginalTriangleNormalization

set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace PoincareConjecture.M76.TriangleCorner

private theorem standard_edge_nonreturn {r : Set (ℝ × ℝ)}
    (h : ∀ t : Finset (ℝ × ℝ), (t : Set (ℝ × ℝ)) ⊆ vertices →
      t.card = 2 → ¬ r ⊆ convexHull ℝ (t : Set (ℝ × ℝ))) :
    (¬ r ⊆ {0} ×ˢ Icc (0 : ℝ) 1) ∧
    (¬ r ⊆ Icc (0 : ℝ) 1 ×ˢ {0}) ∧
    (¬ r ⊆ {x ∈ base | x.1 + x.2 = 1}) := by
  classical
  have hl : ({0} ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) =
      convexHull ℝ ({(0, 0), (0, 1)} : Set (ℝ × ℝ)) := by
    rw [convexHull_pair, segment_symm]
    ext x
    rw [TriangleDiskModel.mem_common_edge_iff]
    rfl
  have hb : (Icc (0 : ℝ) 1 ×ˢ {0} : Set (ℝ × ℝ)) =
      convexHull ℝ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)) := by
    rw [convexHull_pair]
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨1 - x.1, x.1, by linarith [hx.2], hx.1, by ring, ?_⟩
      ext <;> simp [show x.2 = 0 from hy]
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      change (0 ≤ a * 0 + b * 1 ∧ a * 0 + b * 1 ≤ 1) ∧ a * 0 + b * 0 = 0
      exact ⟨⟨by nlinarith, by nlinarith⟩, by ring⟩
  have hd : {x ∈ base | x.1 + x.2 = 1} =
      convexHull ℝ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
    rw [convexHull_pair]
    ext x
    constructor
    · rintro ⟨hx, he⟩
      rw [base_eq_triangle, TriangleDiskModel.mem_right_region_iff] at hx
      refine ⟨x.1, x.2, hx.1, hx.2.1, he, ?_⟩
      ext <;> simp
    · rintro ⟨a, b, ha, hb, hab, rfl⟩
      rw [mem_ofPred_eq, base_eq_triangle, TriangleDiskModel.mem_right_region_iff]
      change (0 ≤ a * 1 + b * 0 ∧ 0 ≤ a * 0 + b * 1 ∧
        a * 1 + b * 0 + (a * 0 + b * 1) ≤ 1) ∧
        a * 1 + b * 0 + (a * 0 + b * 1) = 1
      simpa only [mul_one, mul_zero, add_zero, zero_add] using ⟨⟨ha, hb, hab.le⟩, hab⟩
  have h01 : ¬ r ⊆ convexHull ℝ ({(0, 0), (0, 1)} : Set (ℝ × ℝ)) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      h {(0, 0), (0, 1)} (by simp [vertices]) (by norm_num)
  have h02 : ¬ r ⊆ convexHull ℝ ({(0, 0), (1, 0)} : Set (ℝ × ℝ)) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      h {(0, 0), (1, 0)} (by simp [vertices]) (by norm_num)
  have h12 : ¬ r ⊆ convexHull ℝ ({(1, 0), (0, 1)} : Set (ℝ × ℝ)) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using
      h {(1, 0), (0, 1)} (by simp [vertices]) (by norm_num)
  exact ⟨hl ▸ h01, hb ▸ h02, hd ▸ h12⟩

theorem exists_original_normal_family_coordinates
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (d r : ι → Set E) (hd : ∀ i, IsFinitePLBallPair ℝ (d i) (r i))
    (hsub : ∀ i, d i ⊆ convexHull ℝ (s : Set E))
    (hrim : ∀ i, r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    (hdis : Pairwise fun i j => Disjoint (d i) (d j))
    (hvertex : ∀ i, Disjoint (d i) (s : Set E))
    (hnr : ∀ i, ∀ t : Finset E, t ⊆ s → t.card = 2 → ¬ r i ⊆ convexHull ℝ (t : Set E)) :
    ∃ (F : (ℝ × ℝ) →ᴬ[ℝ] E) (R : E →ᴬ[ℝ] (ℝ × ℝ)) (p q : ι → ℝ × ℝ),
      Function.LeftInverse R F ∧
      EqOn (F ∘ R) id (convexHull ℝ (s : Set E)) ∧
      F '' base = convexHull ℝ (s : Set E) ∧ F '' vertices = (s : Set E) ∧
      F '' frontier base = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ∧
      (∀ i, F '' (R '' d i) = d i) ∧
      (∀ i, IsFinitePLBallPair ℝ (R '' d i) {p i, q i}) ∧
      (∀ i, p i ≠ q i) ∧ (∀ i, R '' d i ⊆ base) ∧
      (∀ i, ({p i, q i} : Set (ℝ × ℝ)) = (R '' d i) ∩ frontier base) ∧
      (Pairwise fun i j => Disjoint (R '' d i) (R '' d j)) ∧
      (∀ i, p i ∉ vertices) ∧ (∀ i, q i ∉ vertices) ∧
      (∀ i, ¬ ({p i, q i} : Set (ℝ × ℝ)) ⊆ {0} ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ i, ¬ ({p i, q i} : Set (ℝ × ℝ)) ⊆ Icc (0 : ℝ) 1 ×ˢ {0}) ∧
      (∀ i, ¬ ({p i, q i} : Set (ℝ × ℝ)) ⊆ {x ∈ base | x.1 + x.2 = 1}) := by
  classical
  obtain ⟨F, R, hRF, hFR, hface, hverts, hfront⟩ := exists_original_triangle_normalization K hs hs3
  choose u v huv huvR using fun i => (hd i).exists_boundary_eq_pair
  let p := fun i => R (u i)
  let q := fun i => R (v i)
  have hFR' {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) : F (R x) = x := hFR hx
  have hRi : InjOn R (convexHull ℝ (s : Set E)) := by
    intro x hx y hy he
    exact (hFR' hx).symm.trans ((congrArg F he).trans (hFR' hy))
  have hrestore (i : ι) : F '' (R '' d i) = d i := by
    rw [image_image]
    exact (image_congr fun x hx => hFR (hsub i hx)).trans (image_id _)
  have hu (i : ι) : u i ∈ d i := (hd i).1 ((huvR i).symm.subset (by simp))
  have hv (i : ι) : v i ∈ d i := (hd i).1 ((huvR i).symm.subset (by simp))
  have hpair (i : ι) : R '' r i = ({p i, q i} : Set (ℝ × ℝ)) := by
    rw [huvR i]
    simp only [image_insert_eq, image_singleton, p, q]
  have hRsub (i : ι) : R '' d i ⊆ base := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := hface.symm.subset (hsub i hx)
    rw [← he, hRF y]
    exact hy
  have hRrim (i : ι) : ({p i, q i} : Set (ℝ × ℝ)) = (R '' d i) ∩ frontier base := by
    rw [← hpair i, hrim i]
    ext x
    constructor
    · rintro ⟨y, ⟨hyd, hyf⟩, rfl⟩
      obtain ⟨z, hz, he⟩ := hfront.symm.subset hyf
      exact ⟨mem_image_of_mem R hyd, by rwa [← he, hRF z]⟩
    · rintro ⟨⟨y, hy, rfl⟩, hrf⟩
      exact ⟨y, ⟨hy, hFR' (hsub i hy) ▸ hfront.subset (mem_image_of_mem F hrf)⟩, rfl⟩
  have havoid (i : ι) : Disjoint (R '' d i) vertices := by
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hvx
    exact disjoint_left.mp (hvertex i) hx
      (hFR' (hsub i hx) ▸ hverts.subset (mem_image_of_mem F hvx))
  have hnonreturn (i : ι) := standard_edge_nonreturn (r := ({p i, q i} : Set (ℝ × ℝ)))
    (fun t ht ht2 hbad => by
      let a := t.image F
      have has : a ⊆ s := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact hverts.subset (mem_image_of_mem F (ht hy))
      have ha2 : a.card = 2 := (Finset.card_image_of_injective _ hRF.injective).trans ht2
      apply hnr i a has ha2
      intro x hx
      have hxR := hpair i ▸ mem_image_of_mem R hx
      have hFx := (F.toAffineMap.image_convexHull (t : Set (ℝ × ℝ))).subset
        (mem_image_of_mem F (hbad hxR))
      rw [hFR' (hsub i ((hd i).1 hx))] at hFx
      change x ∈ convexHull ℝ (F '' (t : Set (ℝ × ℝ))) at hFx
      simpa only [a, Finset.coe_image] using hFx)
  refine ⟨F, R, p, q, hRF, hFR, hface, hverts, hfront, hrestore, ?_, ?_, hRsub,
    hRrim, ?_, ?_, ?_, fun i => (hnonreturn i).1,
    fun i => (hnonreturn i).2.1, fun i => (hnonreturn i).2.2⟩
  · intro i
    rw [← hpair i]
    exact (hd i).affine_image R (hRi.mono (hsub i))
  · intro i he
    exact huv i (hRi (hsub i (hu i)) (hsub i (hv i)) he)
  · intro i j hij
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have hyx := hRi (hsub j hy) (hsub i hx) he
    exact disjoint_left.mp (hdis hij) hx (hyx ▸ hy)
  · intro i hpi
    exact disjoint_left.mp (havoid i) (mem_image_of_mem R (hu i)) hpi
  · intro i hqi
    exact disjoint_left.mp (havoid i) (mem_image_of_mem R (hv i)) hqi

end PoincareConjecture.M76.TriangleCorner
